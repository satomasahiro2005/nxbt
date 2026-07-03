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
    """Forward Switch rumble to a real Joy-Con L over raw L2CAP.

    NXBT builds ControllerServer in the parent process, then forks a child that
    runs mainloop(). Threads started here stay in the parent and never see
    Switch rumble reports. Joy-Con connection attempts are therefore launched
    lazily from the child, while rumble writes stay in handle_switch_report().
    """

    _NEUTRAL_HALF = bytes([0x00, 0x01, 0x40, 0x40])
    _NEUTRAL = _NEUTRAL_HALF + _NEUTRAL_HALF
    _SILENT = (bytes([0x00, 0x00, 0x00, 0x00]), _NEUTRAL_HALF)
    _RUMBLE_REPORTS = (0x01, 0x10, 0x11)
    _JOYCON_L = "BC:74:4B:8B:98:82"
    _SOL_BLUETOOTH = 274
    _BT_SECURITY = 4
    _BT_SECURITY_LOW = 1
    _SOL_L2CAP = 6
    _L2CAP_LM = 3
    _L2CAP_LM_MASTER = 0x0001

    def __init__(self, logger):
        self.logger = logger
        self.control = None
        self.interrupt = None
        self.timer = 0
        self.last_write_at = 0.0
        self.next_connect_at = 0.0
        self.connecting = False
        self.led_retry_until = 0.0
        self.last_led_at = 0.0
        self.led_writes = 0
        self._led_ack_seen = False
        self._led_ack_at = 0.0
        self.report_mode_retry_until = 0.0
        self.last_report_mode_at = 0.0
        self.report_mode_writes = 0
        self._joycon_30_seen = False
        self.last_rumble_bytes = self._NEUTRAL
        self.last_switch_report_at = 0.0
        self.last_switch_active_at = 0.0
        self._last_rx_rumble = None
        self._dbg_change = 0
        self.connect_fail_count = 0
        self.last_connect_fail_log = 0.0
        self._dbg_seen = 0
        self._dbg_raw = 0
        self._dbg_rx = 0
        self._dbg_sent = 0
        self._reports = 0
        self._active_reports = 0
        self._sent = 0
        self._sent_active = 0
        self._write_fails = 0
        self._last_stat_at = 0.0
        self._last_reports = 0
        self._last_active_reports = 0
        self._last_sent = 0
        self._last_sent_active = 0
        self.capture_marker = "/tmp/rumble_capture_on"
        self.capture_log = "/tmp/rumble_capture.log"
        self.capture_until = 0.0
        self.capture_count = 0
        self._joycon_rx_seen = 0
        self._last_joycon_vibrator = None
        self.last_vib_ack = None
        self._test_pulse_stop_at = 0.0
        self._dbg("bridge init fork-safe sync")

    def _dbg(self, msg):
        try:
            with open("/tmp/rumble_debug.log", "a") as f:
                f.write("%.3f [pid %d] %s\n" % (time.time(), os.getpid(), msg))
        except OSError:
            pass

    def _capture_rx(self, source, report_id, rumble, mapped, active, dt_ms,
                    allow_connect):
        now = time.time()
        if now >= self.capture_until and os.path.exists(self.capture_marker):
            try:
                os.unlink(self.capture_marker)
            except OSError:
                pass
            self.capture_until = now + 45.0
            self.capture_count = 0
            try:
                with open(self.capture_log, "a") as f:
                    f.write("%.3f [pid %d] capture start 45s\n"
                            % (now, os.getpid()))
                    f.write("time,pid,source,id,raw,mono,active,dt_ms,conn,allow\n")
            except OSError:
                pass

        if now >= self.capture_until or self.capture_count >= 4000:
            return

        self.capture_count += 1
        try:
            with open(self.capture_log, "a") as f:
                f.write("%.6f,%d,%s,0x%02x,%s,%s,%d,%.3f,%d,%d\n"
                        % (now, os.getpid(), source, report_id, rumble.hex(),
                           mapped.hex(), 1 if active else 0, dt_ms,
                           1 if self.interrupt is not None else 0,
                           1 if allow_connect else 0))
        except OSError:
            pass

    def _mono_rumble(self, data):
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

    def _stat(self):
        now = time.time()
        if now - self._last_stat_at < 1.0:
            return
        self._last_stat_at = now

        reports_delta = self._reports - self._last_reports
        active_delta = self._active_reports - self._last_active_reports
        sent_delta = self._sent - self._last_sent
        sent_active_delta = self._sent_active - self._last_sent_active
        self._last_reports = self._reports
        self._last_active_reports = self._active_reports
        self._last_sent = self._sent
        self._last_sent_active = self._sent_active

        self._dbg(
            "stat conn=%d connecting=%d reports=%d dreports=%d active=%d "
            "dactive=%d sent=%d dsent=%d sent_active=%d dsent_active=%d fails=%d"
            % (
                1 if self.interrupt is not None else 0,
                1 if self.connecting else 0,
                self._reports,
                reports_delta,
                self._active_reports,
                active_delta,
                self._sent,
                sent_delta,
                self._sent_active,
                sent_active_delta,
                self._write_fails,
            )
        )

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
        sock.connect((self._JOYCON_L, psm))
        sock.setblocking(False)
        return sock

    def _open(self):
        if self.interrupt is not None:
            return True
        # Pause flag: stop hammering Joy-Con connects (they can leave zombie
        # paging state that starves the Switch link -> input lag).
        if os.path.exists("/tmp/jc_off"):
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
            self._set_low_traffic_report_mode(interrupt)
            self._start_led_retry()
            self._set_player_lights(interrupt)
            self.connect_fail_count = 0
            self._dbg("joycon connected + vibration enabled")
            self.logger.info("Raw Joy-Con L2CAP rumble ready")
        except OSError as e:
            now = time.time()
            if self.connect_fail_count < 5 or now - self.last_connect_fail_log > 15.0:
                self._dbg("connect fail errno=%s %s" % (e.errno, e.strerror))
                self.last_connect_fail_log = now
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
        report = bytes([0xA2, 0x01, self._next_timer()]) \
            + self._NEUTRAL + bytes([0x48, 0x01])
        report = report.ljust(49, b"\x00")
        sock.send(report)

    def _start_led_retry(self):
        self.led_retry_until = time.time() + 12.0
        self.last_led_at = 0.0
        self.led_writes = 0
        self._led_ack_seen = False
        self._led_ack_at = 0.0

    def _set_player_lights(self, sock=None):
        if sock is None:
            sock = self.interrupt
        if sock is None:
            return
        report = bytes([0xA2, 0x01, self._next_timer()]) \
            + self._NEUTRAL + bytes([0x30, 0x09])
        report = report.ljust(49, b"\x00")
        sent = sock.send(report)
        self.led_writes += 1
        if self.led_writes <= 12:
            self._dbg("set player lights 1001 sent=%s" % sent)

    def _set_low_traffic_report_mode(self, sock=None):
        if sock is None:
            sock = self.interrupt
        if sock is None:
            return
        report = bytes([0xA2, 0x01, self._next_timer()]) \
            + self._NEUTRAL + bytes([0x03, 0x3F])
        report = report.ljust(49, b"\x00")
        sent = sock.send(report)
        self.report_mode_writes += 1
        if self.report_mode_writes <= 20:
            self._dbg("set report mode 0x3F sent=%s" % sent)

    def _start_report_mode_retry(self):
        self.report_mode_retry_until = time.time() + 8.0
        self.last_report_mode_at = 0.0
        self.report_mode_writes = 0
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
                self._write_fails += 1
                self._dbg("joycon rx fail errno=%s %s" % (e.errno, e.strerror))
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
                if subcmd == 0x30 and ack & 0x80 and not self._led_ack_seen:
                    self._led_ack_seen = True
                    self._led_ack_at = time.time()
                    self.led_retry_until = 0.0
                    self._dbg("player lights ack 0x%02x" % ack)
            vibrator = data[13] if len(data) > 13 else None
            if vibrator is not None and report_id in (0x21, 0x30, 0x31, 0x32, 0x33):
                self.last_vib_ack = vibrator
            changed = vibrator != self._last_joycon_vibrator
            if changed:
                self._last_joycon_vibrator = vibrator
            if self._joycon_rx_seen < 120 or changed:
                self._joycon_rx_seen += 1
                vib_text = "--" if vibrator is None else "0x%02x" % vibrator
                self._dbg(
                    "joycon_rx id=0x%02x vib=%s len=%d raw24=%s"
                    % (report_id, vib_text, len(data), bytes(data[:24]).hex())
                )

    def get_pro_vibrator_report(self, fallback):
        # The vibrator ack is generated inside ControllerProtocol from the
        # Switch's own output reports (_update_vibrator_ack): passing through
        # the real Joy-Con's ack byte is wrong twice over -- it advertises a
        # single-motor (0x30-base) controller, and it acks the frames WE
        # forwarded, not the frames the Switch sent to the virtual Pro. The
        # real ack (last_vib_ack) is still logged for reference.
        return fallback

    def _write_rumble(self, rumble_bytes):
        # Airtime throttle: the Joy-Con keeps vibrating its current state, so
        # re-sending identical frames only steals radio time from the Switch
        # link (input latency jitter on the shared adapter). Forward changes
        # immediately, plus a 1 Hz keepalive.
        rb = bytes(rumble_bytes)
        if (rb == getattr(self, "last_rumble_bytes", None)
                and time.time() - getattr(self, "last_write_at", 0.0) < 1.0):
            return
        if not self._open():
            return
        report = bytes([0xA2, 0x10, self._next_timer()]) + bytes(rumble_bytes)
        try:
            self.interrupt.send(report)
            self.last_rumble_bytes = bytes(rumble_bytes)
            self._sent += 1
            self.last_write_at = time.time()
            if self._is_active(rumble_bytes):
                self._sent_active += 1
            if rumble_bytes != self._NEUTRAL and self._dbg_sent < 80:
                self._dbg_sent += 1
                self._dbg("sent rumble %s" % bytes(rumble_bytes).hex())
        except OSError as e:
            self._write_fails += 1
            self._dbg("write fail errno=%s %s" % (e.errno, e.strerror))
            self.close()

    def handle_switch_report(self, report, allow_connect=True, source="main"):
        if report and self._dbg_seen < 120:
            self._dbg_seen += 1
            try:
                report_id = report[1] if len(report) > 1 else -1
                self._dbg(
                    "seen src=%s len=%d id=0x%02x raw16=%s"
                    % (source, len(report), report_id, bytes(report[:16]).hex())
                )
            except (TypeError, ValueError):
                self._dbg("seen malformed %r" % (report,))
        if not report or len(report) < 11 or report[0] != 0xA2:
            self.tick()
            return
        if report[1] not in self._RUMBLE_REPORTS:
            self.tick()
            return

        self._reports += 1
        now = time.time()
        report_dt_ms = 0.0
        if self.last_switch_report_at:
            report_dt_ms = (now - self.last_switch_report_at) * 1000.0
        self.last_switch_report_at = now

        rumble = bytes(report[3:11])
        mapped = self._mono_rumble(rumble)
        active = self._is_active(rumble)
        self._capture_rx(source, report[1], rumble, mapped, active,
                         report_dt_ms, allow_connect)
        if rumble != self._last_rx_rumble:
            self._last_rx_rumble = rumble
            if self._dbg_change < 200:
                self._dbg_change += 1
                self._dbg(
                    "rxchange src=%s id=0x%02x raw=%s mono=%s active=%d "
                    "dt_ms=%.1f conn=%d allow=%d"
                    % (source, report[1], rumble.hex(), mapped.hex(),
                       1 if active else 0, report_dt_ms,
                       1 if self.interrupt is not None else 0,
                       1 if allow_connect else 0)
                )
        if self._dbg_rx < 80 and (active or self.interrupt is not None):
            self._dbg_rx += 1
            self._dbg(
                "rx src=%s id=0x%02x raw=%s mono=%s active=%d conn=%d allow=%d"
                % (source, report[1], rumble.hex(), mapped.hex(),
                   1 if active else 0,
                   1 if self.interrupt is not None else 0,
                   1 if allow_connect else 0)
            )
        if active:
            self._active_reports += 1
            self.last_switch_active_at = now
            if self._dbg_raw < 80:
                self._dbg_raw += 1
                self._dbg(
                    "switch active src=%s id=0x%02x raw=%s mono=%s dt_ms=%.1f conn=%d allow=%d"
                    % (source, report[1], rumble.hex(), mapped.hex(), report_dt_ms,
                       1 if self.interrupt is not None else 0,
                       1 if allow_connect else 0)
                )
        if allow_connect:
            self._write_rumble(mapped)
        elif active and self._dbg_sent < 80:
            self._dbg_sent += 1
            self._dbg("drop setup rumble src=%s %s" % (source, mapped.hex()))
        self._stat()

    def tick(self):
        if self.interrupt is None:
            self._open()
        else:
            self._drain_joycon_rx()
            now = time.time()
            if os.path.exists("/tmp/joycon_test_pulse"):
                try:
                    os.unlink("/tmp/joycon_test_pulse")
                except OSError:
                    pass
                self._dbg("test pulse start")
                self._write_rumble(bytes.fromhex("c318606dc318606d"))
                self._test_pulse_stop_at = now + 0.12
            if self._test_pulse_stop_at and now >= self._test_pulse_stop_at:
                self._dbg("test pulse stop")
                self._write_rumble(self._NEUTRAL)
                self._test_pulse_stop_at = 0.0
            if (now < self.led_retry_until
                    and now - self.last_led_at > 0.5):
                self.last_led_at = now
                try:
                    self._set_player_lights()
                except OSError as e:
                    self._write_fails += 1
                    self._dbg("led write fail errno=%s %s" % (e.errno, e.strerror))
                    self.close()
                    self._stat()
                    return
            if (not self._joycon_30_seen
                    and now < self.report_mode_retry_until
                    and now - self.last_report_mode_at > 0.5):
                self.last_report_mode_at = now
                try:
                    self._set_low_traffic_report_mode()
                except OSError as e:
                    self._write_fails += 1
                    self._dbg("report mode write fail errno=%s %s" % (e.errno, e.strerror))
                    self.close()
        self._stat()

    def preconnect(self, timeout=45.0):
        self._dbg("joycon preconnect start timeout=%.1f" % timeout)
        deadline = time.time() + timeout
        while time.time() < deadline:
            self.tick()
            now = time.time()
            if (self.interrupt is not None
                    and self._joycon_30_seen
                    and self._led_ack_seen
                    and now - self._led_ack_at > 0.25):
                vib = self._last_joycon_vibrator
                vib_text = "--" if vib is None else "0x%02x" % vib
                self._dbg("joycon preconnect ready vib=%s led_ack=1" % vib_text)
                return True
            time.sleep(0.02)
        self._dbg(
            "joycon preconnect timeout conn=%d mode30=%d led_ack=%d"
            % (1 if self.interrupt is not None else 0,
               1 if self._joycon_30_seen else 0,
               1 if self._led_ack_seen else 0)
        )
        return False

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
                with open('/tmp/input_rate') as f:
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
                    self.rumble.handle_switch_report(next_reply, source="main")
                    self.protocol.process_commands(next_reply)
                    self.protocol.vibrator_report = self.rumble.get_pro_vibrator_report(
                        self.protocol.vibrator_report)
                    msg = self.protocol.get_report()
                    if msg[1] != 0x00:
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

            # Set Direct Input
            if self.state["direct_input"]:
                self.input.set_controller_input(self.state["direct_input"])

            if reply is None or sent_drain_reply:
                self.protocol.process_commands(None)
            self.input.set_protocol_input(state=self.state)

            self.protocol.vibrator_report = self.rumble.get_pro_vibrator_report(
                self.protocol.vibrator_report)
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
                # /tmp/input_rate (default 132 = stock keepalive ~2 s).
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

                        self.rumble.handle_switch_report(reply, allow_connect=False, source="reconnect")
                        self.protocol.process_commands(reply)
                        self.protocol.vibrator_report = self.rumble.get_pro_vibrator_report(
                            self.protocol.vibrator_report)
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

                itr, itr_address = s_itr.accept()
                ctrl, ctrl_address = s_ctrl.accept()

                self._crw_running = False

                # Send an empty input report to the Switch to prompt a reply
                self.protocol.process_commands(None)
                self.protocol.vibrator_report = self.rumble.get_pro_vibrator_report(
                    self.protocol.vibrator_report)
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

                    self.rumble.handle_switch_report(reply, allow_connect=False, source="pairing")
                    self.protocol.process_commands(reply)
                    self.protocol.vibrator_report = self.rumble.get_pro_vibrator_report(
                        self.protocol.vibrator_report)
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
        self.protocol.vibrator_report = self.rumble.get_pro_vibrator_report(
            self.protocol.vibrator_report)
        msg = self.protocol.get_report()
        itr.sendall(msg)

        # Setting interrupt connection as non-blocking
        # In this case, non-blocking means it throws a "BlockingIOError"
        # for sending and receiving, instead of blocking
        fcntl.fcntl(itr, fcntl.F_SETFL, os.O_NONBLOCK)

        return itr, ctrl

    def _on_exit(self):
        self.bt.reset_address()
