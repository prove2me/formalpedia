-- Prove2me | Theorems.Thm_BitDFT_unpackerSkip_stays
-- name    : BitDFT.unpackerSkip_stays
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:23:40.374736+00:00
-- url     : https://prove2.me/theorems/b0c769c8-431b-4865-bd7a-bdb44f74ca0a
-- title:
--   The skip phase never hands over to the counter countdown
-- statement:
--   The unpacking machine's header parse runs: count the unary prefix of the encoding of $r$, step past the terminating $0$, then count the binary digits that follow, using a second counter. The third phase is meant to be a single step.
--
--   The theorem records what that phase actually does: once the machine is in it, every later transition leaves it there. The phase's rule steps the input head right and does not change phase, so the machine marches along the input and never enters the phase that is supposed to consume the binary digits. Consequently the encoding of $r$ is never read, the counter that should hold it is never built, and every later phase that depends on that count runs with nothing to count.
--
--   This is the third defect of the machine family, after `BitDFT.unpackerMachine_stuck` (the machine could not leave its end marker) and `BitDFT.unpackerMachine_counter_blank` (every recorded mark was dropped). It is the same species again: a phase written as if it were a one-step hand-off, but specified as a self-loop.
--
--   The cure is one line: the phase's rule must return the successor phase instead of its own. With that change the machine reaches the binary-digit countdown, whose single-step rules are already stated and proved in `BitDFT.unpackerSpec_rBinary_mark` and its companions once the counter has content.
-- source:
--   Internal: third defect report for the unpacking machine, found while setting up the rBinary countdown of Prove2me's BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98).

import Definitions.Def_BitDFT_unpackerMachineV2

theorem BitDFT.unpackerSkip_stays (k : ℕ) (c : BitDFT.Unpacker.machine.Cfg) (g κ s : Bool)
    (h : c.state = some ⟨BitDFT.Unpacker.Ph.rSkipFalse, g, κ, s⟩) :
    (BitDFT.Unpacker.machine.step^[k] c).state
      = some ⟨BitDFT.Unpacker.Ph.rSkipFalse, g, κ, s⟩ := by sorry
