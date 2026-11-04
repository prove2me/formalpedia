-- Prove2me | Theorems.Thm_BitDFT_unpackerMachine_counter_blank
-- name    : BitDFT.unpackerMachine_counter_blank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:29:40.327234+00:00
-- url     : https://prove2.me/theorems/838805e1-85d5-473a-8302-26231491b09e
-- title:
--   The unpacking machine drops every unary mark it tries to record
-- statement:
--   The `rUnary` phase of the unpacking machine consumes one unary mark from the input and records it on its own counter tape, so that the count of $\beta$'s bit length can be carried around. It does so in the order *write, then move*: the symbol under the counter head is rewritten as a mark and the head then steps right.
--
--   The counter tape starts with its head on cell $0$, which holds the end marker $\triangleright$. The guard that enforces the model's rule that the end marker is never overwritten therefore suppresses the write, and the phase itself then moves the head on. The result is that the mark is silently lost: after the machine's first three transitions the first cell of the counter tape is still blank.
--
--   This is a defect of the same family as the one recorded in `BitDFT.unpackerMachine_stuck`. Its effect is that the counter never holds a count, so the phases that consume the counter — the digit loop and the counter reload — run with an empty tape and the machine never produces a digit. The cure is to advance each head off the end marker before the first write, for instance by a leading phase that steps every head one cell right, so that every write-then-move happens on a cell that is not the marker.
-- source:
--   Internal: second defect report for the unpacking machine, found while proving the run induction for the rUnary loop of Prove2me's BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98).

import Definitions.Def_BitDFT_unpackerMachineV2

theorem BitDFT.unpackerMachine_counter_blank (t y : List Bool) :
    (BitDFT.Unpacker.machine.step^[3] (BitDFT.Unpacker.machine.initCfg (true :: t) y)).cells
      (⟨5, by delta BitDFT.Unpacker.machine; norm_num⟩ : Fin BitDFT.Unpacker.machine.k) 1
      = BitDFT.Unpacker.machine.blank := by sorry
