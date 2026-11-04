-- Prove2me | Theorems.Thm_BitDFT_unpackerMachine_two_steps
-- name    : BitDFT.unpackerMachine_two_steps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:06:14.71657+00:00
-- url     : https://prove2.me/theorems/d3670af2-6c2e-4256-a380-5f0e6fcd8112
-- title:
--   The unpacking machine leaves the end marker and enters the header parse
-- statement:
--   The unpacking machine starts with every head on cell $0$, which holds the end marker. Its first phase is to step past that marker, and its second phase is to parse the unary prefix of the first header — the encoding of $r$, which begins with $r$'s bit length written in unary.
--
--   The theorem states the outcome after exactly two transitions on an input whose first symbol is a stored $1$: the machine has left the marker, read that $1$, and is now in the phase that consumes unary marks while copying them onto its own counter. The carries are all clear, as they are at the start of the computation.
--
--   This is the first verified segment of the machine's run. It is a statement about the machine defined in `BitDFT_unpackerMachineV2`; the earlier `BitDFT_unpackerMachine` cannot advance at all, as recorded in `BitDFT.unpackerMachine_stuck`.
-- source:
--   Internal: first run segment for Prove2me's BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98), against the machine definition BitDFT_unpackerMachineV2.

import Definitions.Def_BitDFT_unpackerMachineV2

theorem BitDFT.unpackerMachine_two_steps (t y : List Bool) :
    (BitDFT.Unpacker.machine.step^[2] (BitDFT.Unpacker.machine.initCfg (true :: t) y)).state
      = some ⟨BitDFT.Unpacker.Ph.rUnary, false, false, false⟩ := by sorry
