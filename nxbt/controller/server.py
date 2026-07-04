import socket
import fcntl
import os
import time
import queue
import logging
import traceback
import atexit
from threading import Thread
import statistics as stat

from .controller import Controller, ControllerTypes
from ..bluez import BlueZ, find_devices_by_alias
from .protocol import ControllerProtocol
from .input import InputParser
from .utils import format_msg_controller, format_msg_switch


class RawJoyConRumbleBridge():
    """Forward the Switch's rumble to a real Joy-Con over raw L2CAP.

    The console's HD rumble frames (output reports 0x01/0x10/0x11) are
    remapped for the Joy-Con's single motor and written to its interrupt
    channel, so games physically rumble a real Joy-Con while input comes
    from any controller NXBT emulates.

    Configuration: the Joy-Con's Bluetooth MAC is read from the
    NXBT_JOYCON_MAC environment variable, or from the first existing file
    of /etc/nxbt/joycon_mac and ~/.config/nxbt/joycon_mac. Without a MAC
    the bridge stays inert. Touch /tmp/nxbt_joycon_off to pause connection
    attempts at runtime (a failed sync can leave zombie paging state that
    starves the Switch link).

    NXBT builds ControllerServer in the parent process, then forks a child
    that runs mainloop(). Threads started in __init__ would stay in the
    parent and never see Switch rumble reports, so connection attempts are
    launched lazily from the child's tick()/handle_switch_report() calls.
    """

    _NEUTRAL_HALF = bytes([0x00, 0x01, 0x40, 0x40])
    _NEUTRAL = _NEUTRAL_HALF + _NEUTRAL_HALF
    _RUMBLE_REPORTS = (0x01, 0x10, 0x11)
    _PAUSE_FLAG = "/tmp/nxbt_joycon_off"
    _CONNECT_TRIGGER = "/tmp/nxbt_joycon_connect"
    _SOL_BLUETOOTH = 274
    _BT_SECURITY = 4
    _BT_SECURITY_LOW = 1
    _SOL_L2CAP = 6
    _L2CAP_LM = 3
    _L2CAP_LM_MASTER = 0x0001

    def __init__(self, logger):
        self.logger = logger
        self.joycon_address = self._resolve_joycon_address()
        self._born = time.time()
        self.control = None
        self.interrupt = None
        self.timer = 0
        self.last_write_at = 0.0
        self.last_rumble_bytes = self._NEUTRAL
        self.next_connect_at = 0.0
        self.connecting = False
        self.connect_fail_count = 0
        self.led_retry_until = 0.0
        self.last_led_at = 0.0
        self._led_ack_seen = False
        self.report_mode_retry_until = 0.0
        self.last_report_mode_at = 0.0
        self._joycon_30_seen = False
        if self.joycon_address is None:
            self.logger.info(
                "Joy-Con rumble bridge inert: no MAC configured "
                "(set NXBT_JOYCON_MAC or /etc/nxbt/joycon_mac)")

    def _resolve_joycon_address(self):
        candidates = [os.environ.get("NXBT_JOYCON_MAC")]
        for path in ("/etc/nxbt/joycon_mac",
                     os.path.expanduser("~/.config/nxbt/joycon_mac")):
            try:
                with open(path) as f:
                    candidates.append(f.read())
            except OSError:
                continue
        for value in candidates:
            if not value:
                continue
            value = value.strip().upper()
            if len(value) == 17 and value.count(":") == 5:
                return value
        return None

    def _mono_rumble(self, data):
        # The console drives a Pro Controller's two motors in alternating
        # frames (left = bytes 0:4, right = bytes 4:8). A single Joy-Con has
        # one motor, so forward whichever half is actually driven, duplicated
        # into both halves.
        if not self._is_active(data):
            return self._NEUTRAL

        left, right = data[0:4], data[4:8]
        if self._is_active(left + left):
            mono = left
        elif self._is_active(right + right):
            mono = right
        else:
            mono = self._NEUTRAL_HALF
        return mono + mono

    def _is_active(self, data):
        if data == self._NEUTRAL or data == b"\x00" * 8:
            return False

        zero = bytes([0x00, 0x00, 0x00, 0x00])
        for offset in (0, 4):
            motor = data[offset:offset + 4]
            if motor in (self._NEUTRAL_HALF, zero):
                continue
            high_amp = motor[1] & 0xFE
            low_amp = (motor[2] & 0x80) or max(0, motor[3] - 0x40)
            if high_amp or low_amp:
                return True
        return False

    def _connect_channel(self, psm):
        sock = socket.socket(
            socket.AF_BLUETOOTH,
            socket.SOCK_SEQPACKET,
            socket.BTPROTO_L2CAP)
        sock.settimeout(2.0)
        sock.setsockopt(
            self._SOL_BLUETOOTH,
            self._BT_SECURITY,
            bytes([self._BT_SECURITY_LOW, 0]))
        sock.setsockopt(
            self._SOL_L2CAP,
            self._L2CAP_LM,
            self._L2CAP_LM_MASTER.to_bytes(4, "little"))
        sock.connect((self.joycon_address, psm))
        sock.setblocking(False)
        return sock

    def _open(self):
        if self.interrupt is not None:
            return True
        if self.joycon_address is None:
            return False
        if os.path.exists(self._PAUSE_FLAG):
            return False
        if not self._paging_allowed():
            return False
        now = time.time()
        if self.connecting or now < self.next_connect_at:
            return False
        self.next_connect_at = now + 6.0
        self.connecting = True
        connector = Thread(target=self._connect_async)
        connector.daemon = True
        connector.start()
        return False

    def _paging_allowed(self):
        # Paging a sleeping Joy-Con occupies the shared radio for ~2 s per
        # attempt, which periodically starves the Switch link (input dies,
        # console drops back to the registration screen) -- even a startup
        # grace window turned out to stab freshly-paired sessions. Page ONLY
        # within 90 s of the trigger file being touched (hold SYNC on the
        # Joy-Con, then: touch /tmp/nxbt_joycon_connect).
        try:
            if time.time() - os.path.getmtime(self._CONNECT_TRIGGER) < 90.0:
                return True
        except OSError:
            pass
        return False

    def _connect_async(self):
        control = None
        interrupt = None
        try:
            self.close()
            control = self._connect_channel(0x11)
            interrupt = self._connect_channel(0x13)
            self.control = control
            self.interrupt = interrupt
            self.last_write_at = time.time()
            self._enable_vibration(interrupt)
            self._start_report_mode_retry()
            self._set_low_traffic_report_mode(interrupt)
            self._start_led_retry()
            self._set_player_lights(interrupt)
            self.connect_fail_count = 0
            self.logger.info("Raw Joy-Con L2CAP rumble ready")
            try:
                os.unlink(self._CONNECT_TRIGGER)
            except OSError:
                pass
        except OSError as e:
            self.logger.debug(
                "Joy-Con connect failed (errno=%s)" % e.errno)
            self.connect_fail_count += 1
            for sock in (interrupt, control):
                if sock is None:
                    continue
                try:
                    sock.close()
                except OSError:
                    pass
            self.next_connect_at = time.time() + min(
                20.0, 6.0 + self.connect_fail_count * 2.0)
        finally:
            self.connecting = False

    def _enable_vibration(self, sock):
        # A real Joy-Con ignores rumble until it receives subcommand
        # 0x48 0x01. 0xA2 is the HIDP DATA/output header required on the
        # interrupt channel.
        report = bytes([0xA2, 0x01, self._next_timer()]) \
            + self._NEUTRAL + bytes([0x48, 0x01])
        report = report.ljust(49, b"\x00")
        sock.send(report)

    def _start_led_retry(self):
        self.led_retry_until = time.time() + 12.0
        self.last_led_at = 0.0
        self._led_ack_seen = False

    def _set_player_lights(self, sock=None):
        if sock is None:
            sock = self.interrupt
        if sock is None:
            return
        report = bytes([0xA2, 0x01, self._next_timer()]) \
            + self._NEUTRAL + bytes([0x30, 0x09])
        report = report.ljust(49, b"\x00")
        sock.send(report)

    def _set_low_traffic_report_mode(self, sock=None):
        # Keep the Joy-Con in simple HID mode (0x3F) instead of the 60 Hz
        # full-report mode (0x30): its input stream is useless here and the
        # extra airtime on a shared adapter causes input latency jitter on
        # the Switch link.
        if sock is None:
            sock = self.interrupt
        if sock is None:
            return
        report = bytes([0xA2, 0x01, self._next_timer()]) \
            + self._NEUTRAL + bytes([0x03, 0x3F])
        report = report.ljust(49, b"\x00")
        sock.send(report)

    def _start_report_mode_retry(self):
        self.report_mode_retry_until = time.time() + 8.0
        self.last_report_mode_at = 0.0
        self._joycon_30_seen = False

    def _next_timer(self):
        self.timer = (self.timer + 1) & 0x0F
        return self.timer

    def _drain_joycon_rx(self):
        if self.interrupt is None:
            return
        for _ in range(8):
            try:
                data = self.interrupt.recv(64)
            except BlockingIOError:
                break
            except OSError as e:
                self.logger.debug(
                    "Joy-Con rx failed (errno=%s)" % e.errno)
                self.close()
                break
            if not data:
                break

            report_id = data[1] if len(data) > 1 and data[0] == 0xA1 else data[0]
            if report_id == 0x30:
                self._joycon_30_seen = True
            elif report_id == 0x21 and len(data) > 15:
                ack = data[14]
                subcmd = data[15]
                if subcmd == 0x30 and ack & 0x80:
                    self._led_ack_seen = True
                    self.led_retry_until = 0.0

    def _write_rumble(self, rumble_bytes):
        # Airtime throttle: re-sending identical frames steals radio time
        # from the Switch link (input latency jitter on the shared adapter),
        # so forward changes immediately and rate-limit repeats. The repeat
        # interval matters: the Joy-Con's motor auto-stops without fresh
        # rumble data (the console normally streams frames continuously), so
        # sustained rumble must be refreshed fast enough to bridge that
        # timeout, while idle neutral only needs a slow keepalive.
        rb = bytes(rumble_bytes)
        keepalive = 0.1 if rb != self._NEUTRAL else 1.0
        if (rb == self.last_rumble_bytes
                and time.time() - self.last_write_at < keepalive):
            return
        if not self._open():
            return
        report = bytes([0xA2, 0x10, self._next_timer()]) + rb
        try:
            self.interrupt.send(report)
            self.last_rumble_bytes = rb
            self.last_write_at = time.time()
        except OSError as e:
            self.logger.debug(
                "Joy-Con rumble write failed (errno=%s)" % e.errno)
            self.close()

    def handle_switch_report(self, report, allow_connect=True):
        if not report or len(report) < 11 or report[0] != 0xA2:
            self.tick()
            return
        if report[1] not in self._RUMBLE_REPORTS:
            self.tick()
            return

        rumble = bytes(report[3:11])
        if allow_connect:
            self._write_rumble(self._mono_rumble(rumble))

    def tick(self):
        if self.joycon_address is None:
            return
        if self.interrupt is None:
            self._open()
            return

        self._drain_joycon_rx()
        now = time.time()
        if (now < self.led_retry_until
                and now - self.last_led_at > 0.5):
            self.last_led_at = now
            try:
                self._set_player_lights()
            except OSError:
                self.close()
                return
        if (not self._joycon_30_seen
                and now < self.report_mode_retry_until
                and now - self.last_report_mode_at > 0.5):
            self.last_report_mode_at = now
            try:
                self._set_low_traffic_report_mode()
            except OSError:
                self.close()

    def close(self):
        if self.interrupt is not None:
            try:
                self.interrupt.send(
                    bytes([0xA2, 0x10, self._next_timer()]) + self._NEUTRAL)
            except OSError:
                pass
        for sock in (self.interrupt, self.control):
            if sock is None:
                continue
            try:
                sock.close()
            except OSError:
                pass
        self.control = None
        self.interrupt = None

class ControllerServer():

    def __init__(self, controller_type, adapter_path="/org/bluez/hci0",
                 state=None, task_queue=None, lock=None, colour_body=None,
                 colour_buttons=None, frequency=66):

        self.logger = logging.getLogger('nxbt')
        # Cache logging level to increase performance on checks
        self.logger_level = self.logger.level

        self.frequency = frequency

        atexit.register(self._on_exit)

        if state:
            self.state = state
        else:
            self.state = {
                "state": "",
                "finished_macros": [],
                "errors": None,
                "direct_input": None
            }

        self.task_queue = task_queue

        self.controller_type = controller_type
        self.colour_body = colour_body
        self.colour_buttons = colour_buttons

        if lock:
            self.lock = lock

        self.reconnect_counter = 0

        # Intializing Bluetooth
        self.bt = BlueZ(adapter_path=adapter_path)

        self.controller = Controller(self.bt, self.controller_type)
        self.protocol = ControllerProtocol(
            self.controller_type,
            self.bt.address,
            colour_body=self.colour_body,
            colour_buttons=self.colour_buttons)

        self.input = InputParser(self.protocol)
        self.rumble = RawJoyConRumbleBridge(self.logger)

        # Debug timekeeping storage array
        self.times = []

        # Initial reconnection overload protection
        self.tick = 1
        self.cached_msg = ''
        self._input_rate = 1
        self._input_rate_checked = 0.0

    def _input_rate_ticks(self):
        now = time.perf_counter()
        if now - self._input_rate_checked > 1.0:
            self._input_rate_checked = now
            try:
                with open('/tmp/nxbt_input_rate') as f:
                    self._input_rate = max(1, min(132, int(f.read().strip())))
            except (OSError, ValueError):
                self._input_rate = 1
        return self._input_rate

    def run(self, reconnect_address=None):
        """Runs the mainloop of the controller server.

        :param reconnect_address: The Bluetooth MAC address of a
        previously connected to Nintendo Switch, defaults to None
        :type reconnect_address: string or list, optional
        """

        self.state["state"] = "initializing"

        self.reconnect_address = reconnect_address

        try:
            # If we have a lock, prevent other controllers
            # from initializing at the same time and saturating the DBus,
            # potentially causing a kernel panic.
            if self.lock:
                self.lock.acquire()
            try:
                self.controller.setup()

                if reconnect_address:
                    try:
                        itr, ctrl = self.reconnect(reconnect_address)
                    except OSError:
                        itr, ctrl = self.connect()
                else:
                    itr, ctrl = self.connect()
            finally:
                if self.lock:
                    self.lock.release()

            self.switch_address = itr.getpeername()[0]
            self.state["last_connection"] = self.switch_address
            self.reconnect_address = self.switch_address

            self.state["state"] = "connected"

            self.mainloop(itr, ctrl)

        except KeyboardInterrupt:
            pass
        except Exception:
            try:
                self.state["state"] = "crashed"
                self.state["errors"] = traceback.format_exc()
                return self.state
            except Exception as e:
                self.logger.debug("Error during graceful shutdown:")
                self.logger.debug(traceback.format_exc())
        finally:
            self.rumble.close()

    def mainloop(self, itr, ctrl):

        duration_start = time.perf_counter()
        period = 1 / self.frequency
        t = time.perf_counter()
        while True:
            # Start timing command processing
            timer_start = time.perf_counter()

            # Drain queued Switch output reports so short rumble bursts are not
            # quantized by the controller input polling rate. Each Switch output
            # report still needs its own timely input report; otherwise multiple
            # subcommand replies can collapse into the final report in this loop.
            reply = None
            sent_drain_reply = False
            for _ in range(16):
                try:
                    next_reply = itr.recv(50)
                    if len(next_reply) > 40:
                        self.logger.debug(format_msg_switch(next_reply))
                    self.rumble.handle_switch_report(next_reply)
                    self.protocol.process_commands(next_reply)
                    msg = self.protocol.get_report()
                    # Only send subcommand replies from the drain; input-
                    # bearing 0x30 reports built here race the per-tick input
                    # application and can carry stale/empty button state
                    # (observed on air as held buttons flickering at the
                    # console's output-report rate).
                    if msg[1] == 0x21:
                        itr.sendall(msg)
                        self.cached_msg = msg[3:]
                        sent_drain_reply = True
                    reply = next_reply
                except BlockingIOError:
                    break
                except ConnectionAbortedError:
                    break
                except OSError as e:
                    itr, ctrl = self.save_connection(e)
                    break
            self.rumble.tick()

            # Getting any inputs from the task queue
            if self.task_queue:
                try:
                    while True:
                        msg = self.task_queue.get_nowait()
                        if msg and msg["type"] == "macro":
                            self.input.buffer_macro(
                                msg["macro"], msg["macro_id"])
                        elif msg and msg["type"] == "stop":
                            self.input.stop_macro(
                                msg["macro_id"], state=self.state)
                        elif msg and msg["type"] == "clear":
                            self.input.clear_macros()
                except queue.Empty:
                    pass

            # Set Direct Input. state is a multiprocessing Manager proxy, so
            # every subscript is a cross-process round trip: fetch once.
            direct_input = self.state["direct_input"]
            if direct_input:
                self.input.set_controller_input(direct_input)

            if reply is None or sent_drain_reply:
                self.protocol.process_commands(None)
            self.input.set_protocol_input(state=self.state)

            msg = self.protocol.get_report()

            if self.logger_level <= logging.DEBUG and reply and len(reply) > 45:
                self.logger.debug(format_msg_controller(msg))

            try:
                # Cache the last packet to prevent overloading the switch
                # with packets on the "Change Grip/Order" menu.
                if msg[3:] != self.cached_msg:
                    itr.sendall(msg)
                    self.cached_msg = msg[3:]
                # Resend the current report at a steady cadence so the
                # console keeps a rumble/output stream going (a real controller
                # streams ~60 Hz). Rate is runtime-tunable in ticks via
                # /tmp/nxbt_input_rate. Default 1 = every tick, matching real
                # hardware; raise it if input latency matters more than
                # rumble delivery cadence.
                elif self.tick >= self._input_rate_ticks():
                    itr.sendall(msg)
                    self.tick = 0
            except BlockingIOError:
                continue
            except OSError as e:
                # Attempt to reconnect to the Switch
                itr, ctrl = self.save_connection(e)

            # Figure out how long it took to process commands
            duration_end = time.perf_counter()
            duration_elapsed = duration_end - duration_start
            duration_start = duration_end
            
            t += period
            time.sleep(max(0,t-time.perf_counter()))

            self.tick += 1

            if self.logger_level <= logging.DEBUG:
                self.times.append(duration_elapsed)
                if len(self.times) > 100:
                    self.times.pop()
                mean_time = stat.mean(self.times)

                self.logger.debug(
                    f"Tick: {self.tick}, Mean Time: {str(1/mean_time)}")


    def save_connection(self, error, state=None):

        while self.reconnect_counter < 2:
            try:
                self.logger.debug("Attempting to reconnect")
                # Reinitialize the protocol
                self.protocol = ControllerProtocol(
                    self.controller_type,
                    self.bt.address,
                    colour_body=self.colour_body,
                    colour_buttons=self.colour_buttons)
                self.input.reassign_protocol(self.protocol)
                if self.lock:
                    self.lock.acquire()
                try:
                    itr, ctrl = self.reconnect(self.switch_address)

                    received_first_message = False
                    while True:
                        # Attempt to get output from Switch
                        try:
                            reply = itr.recv(50)
                            if self.logger_level <= logging.DEBUG and len(reply) > 40:
                                self.logger.debug(format_msg_switch(reply))
                        except BlockingIOError:
                            reply = None

                        if reply:
                            received_first_message = True

                        self.rumble.handle_switch_report(reply, allow_connect=False)
                        self.protocol.process_commands(reply)
                        msg = self.protocol.get_report()

                        if self.logger_level <= logging.DEBUG and reply:
                            self.logger.debug(format_msg_controller(msg))

                        try:
                            itr.sendall(msg)
                        except BlockingIOError:
                            continue

                        # Exit pairing loop when player lights have been set and
                        # vibration has been enabled
                        if (reply and len(reply) > 45 and
                                self.protocol.vibration_enabled and self.protocol.player_number):
                            break

                        # Switch responds to packets slower during pairing
                        # Pairing cycle responds optimally on a 15Hz loop
                        if not received_first_message:
                            time.sleep(1)
                        else:
                            time.sleep(1/15)

                    self.state["state"] = "connected"
                    return itr, ctrl
                finally:
                    if self.lock:
                        self.lock.release()
            except OSError:
                self.reconnect_counter += 1
                self.logger.debug(error)
                time.sleep(0.5)

        # If we can't reconnect, transition to attempting
        # to connect to any Switch.
        self.logger.debug("Connecting to any Switch")
        self.reconnect_counter = 0

        # Reinitialize initial communication overload protections
        self.tick = 1

        # Reinitialize the protocol
        self.protocol = ControllerProtocol(
            self.controller_type,
            self.bt.address,
            colour_body=self.colour_body,
            colour_buttons=self.colour_buttons)
        self.input.reassign_protocol(self.protocol)

        # Since we were forced to attempt a reconnection
        # we need to press the L/SL and R/SR buttons before
        # we can proceed with any input.
        if self.controller_type == ControllerTypes.PRO_CONTROLLER:
            self.input.current_macro_commands = "L R 0.0s".strip(" ").split(" ")
        elif self.controller_type == ControllerTypes.JOYCON_L:
            self.input.current_macro_commands = "JCL_SL JCL_SR 0.0s".strip(" ").split(" ")
        elif self.controller_type == ControllerTypes.JOYCON_R:
            self.input.current_macro_commands = "JCR_SL JCR_SR 0.0s".strip(" ").split(" ")

        if self.lock:
            self.lock.acquire()
        try:
            itr, ctrl = self.connect()
        finally:
            if self.lock:
                self.lock.release()

        self.state["state"] = "connected"

        self.switch_address = itr.getsockname()[0]

        return itr, ctrl

    def connection_reset_watchdog(self):

        connected_devices = []
        connected_devices_count = {}
        while self._crw_running:
            # Check that the adapter is still discoverable
            if not self.bt.discoverable:
                # If not, ensure it's powered, pariable and visible.
                # This action needs to be undertaken due to systemctl
                # performing a delayed reset of the adapter when
                # restarting the Bluetooth daemon.
                time.sleep(0.75) # Wait for systemctl to disable all properties
                self.bt.set_powered(True)
                self.bt.set_pairable(True)
                self.bt.set_pairable_timeout(0)
                self.bt.set_discoverable(True)
                self.bt.set_class("0x02508")

            paths = self.bt.find_connected_devices(alias_filter="Nintendo Switch")
            # Keep track of Switches that connect
            if len(paths) > 0:
                connected_devices = list(set(connected_devices + paths))
            
            # Increment a counter if a Switch connected and disconnected
            disconnected = list(set(connected_devices) - set(paths))
            if len(disconnected) > 0:
                for path in disconnected:
                    if path not in connected_devices_count.keys():
                        connected_devices_count[path] = 1
                    else:
                        connected_devices_count[path] += 1
                connected_devices = list(set(connected_devices) - set(disconnected))
            
            # Delete Switches that connect/disconnect twice.
            # This behaviour is characteristic of connection issues and is corrected
            # by removing the Switch's connection to the system.
            if len(connected_devices_count.keys()) > 0:
                for key in connected_devices_count.keys():
                    if connected_devices_count[key] >= 2:
                        self.logger.debug(
                            "A Nintendo Switch disconnected. Resetting Connection...")
                        self.logger.debug(f"Removing {str(key)}")
                        self.bt.remove_device(key)
                        connected_devices_count[key] = 0

            time.sleep(0.1)

    def connect(self):
        """Configures as a specified controller, pairs with a Nintendo Switch,
        and creates/accepts sockets for communication with the Switch.
        """

        # The controller server will continue attempting to connect
        # to any Nintendo Switch until the connection procedure fully
        # succeeds. This prevents situations where the Switch will
        # disconnect during a connection.
        while True:
            try:
                self.state["state"] = "connecting"

                # Creating control and interrupt sockets
                s_ctrl = socket.socket(
                    family=socket.AF_BLUETOOTH,
                    type=socket.SOCK_SEQPACKET,
                    proto=socket.BTPROTO_L2CAP)
                s_itr = socket.socket(
                    family=socket.AF_BLUETOOTH,
                    type=socket.SOCK_SEQPACKET,
                    proto=socket.BTPROTO_L2CAP)

                # Setting up HID interrupt/control sockets
                try:
                    s_ctrl.bind((self.bt.address, 17))
                    s_itr.bind((self.bt.address, 19))
                except OSError:
                    s_ctrl.bind((socket.BDADDR_ANY, 17))
                    s_itr.bind((socket.BDADDR_ANY, 19))

                s_itr.listen(1)
                s_ctrl.listen(1)

                self.bt.set_discoverable(True)

                # WARNING:
                # A device's class must be set **AFTER** discoverability
                # is set. If it is set before or in a similar timeframe,
                # the class will be reset to the default value.
                self.bt.set_class("0x02508")

                self._crw_running = True
                crw = Thread(target = self.connection_reset_watchdog)
                crw.start()

                # Wait for a Change Grip/Order pairing, but every 15 s also
                # try dialing the remembered console: powering the console
                # on is then enough to reconnect, no menu visit needed.
                s_itr.settimeout(15)
                redialed = False
                while True:
                    try:
                        itr, itr_address = s_itr.accept()
                        ctrl, ctrl_address = s_ctrl.accept()
                        break
                    except socket.timeout:
                        address = getattr(self, "reconnect_address", None)
                        if not address:
                            continue
                        try:
                            itr, ctrl = self.reconnect(address)
                            redialed = True
                            break
                        except OSError:
                            continue
                s_itr.settimeout(None)

                self._crw_running = False

                if redialed:
                    for listener in (s_itr, s_ctrl):
                        try:
                            listener.close()
                        except OSError:
                            pass
                    return itr, ctrl

                # Send an empty input report to the Switch to prompt a reply
                self.protocol.process_commands(None)
                msg = self.protocol.get_report()
                itr.sendall(msg)

                # Setting interrupt connection as non-blocking.
                # In this case, non-blocking means it throws a "BlockingIOError"
                # for sending and receiving, instead of blocking.
                fcntl.fcntl(itr, fcntl.F_SETFL, os.O_NONBLOCK)

                # Mainloop
                received_first_message = False
                while True:
                    # Attempt to get output from Switch
                    try:
                        reply = itr.recv(50)
                        if self.logger_level <= logging.DEBUG and len(reply) > 40:
                            self.logger.debug(format_msg_switch(reply))
                    except BlockingIOError:
                        reply = None

                    if reply:
                        received_first_message = True

                    self.rumble.handle_switch_report(reply, allow_connect=False)
                    self.protocol.process_commands(reply)
                    msg = self.protocol.get_report()

                    if self.logger_level <= logging.DEBUG and reply:
                        self.logger.debug(format_msg_controller(msg))

                    try:
                        itr.sendall(msg)
                    except BlockingIOError:
                        continue

                    # Exit pairing loop when player lights have been set and
                    # vibration has been enabled
                    if (reply and len(reply) > 45 and
                            self.protocol.vibration_enabled and self.protocol.player_number):
                        break

                    # Switch responds to packets slower during pairing
                    # Pairing cycle responds optimally on a 15Hz loop
                    if not received_first_message:
                        time.sleep(1)
                    else:
                        time.sleep(1/15)
                
                break
            except OSError as e:
                self.logger.debug(e)

        self.input.exited_grip_order_menu = False

        return itr, ctrl

    def reconnect(self, reconnect_address):
        """Attempts to reconnect with a Switch at the given address.

        :param reconnect_address: The Bluetooth MAC address of the Switch
        :type reconnect_address: string or list
        """

        def recreate_sockets():
            # Creating control and interrupt sockets
            ctrl = socket.socket(
                family=socket.AF_BLUETOOTH,
                type=socket.SOCK_SEQPACKET,
                proto=socket.BTPROTO_L2CAP)
            itr = socket.socket(
                family=socket.AF_BLUETOOTH,
                type=socket.SOCK_SEQPACKET,
                proto=socket.BTPROTO_L2CAP)

            return itr, ctrl

        self.state["state"] = "reconnecting"

        itr = None
        ctrl = None
        if type(reconnect_address) == list:
            for address in reconnect_address:
                test_itr, test_ctrl = recreate_sockets()
                try:
                    # Setting up HID interrupt/control sockets
                    test_ctrl.connect((address, 17))
                    test_itr.connect((address, 19))

                    itr = test_itr
                    ctrl = test_ctrl
                except OSError:
                    test_itr.close()
                    test_ctrl.close()
                    pass
        elif type(reconnect_address) == str:
            test_itr, test_ctrl = recreate_sockets()

            # Setting up HID interrupt/control sockets
            test_ctrl.connect((reconnect_address, 17))
            test_itr.connect((reconnect_address, 19))

            itr = test_itr
            ctrl = test_ctrl

        if not itr and not ctrl:
            raise OSError("Unable to reconnect to sockets at the given address(es)",
                          reconnect_address)

        fcntl.fcntl(itr, fcntl.F_SETFL, os.O_NONBLOCK)

        # Send an empty input report to the Switch to prompt a reply
        self.protocol.process_commands(None)
        msg = self.protocol.get_report()
        itr.sendall(msg)

        # Setting interrupt connection as non-blocking
        # In this case, non-blocking means it throws a "BlockingIOError"
        # for sending and receiving, instead of blocking
        fcntl.fcntl(itr, fcntl.F_SETFL, os.O_NONBLOCK)

        return itr, ctrl

    def _on_exit(self):
        self.bt.reset_address()
