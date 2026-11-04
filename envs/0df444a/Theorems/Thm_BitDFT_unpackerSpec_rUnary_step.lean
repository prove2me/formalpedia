-- Prove2me | Theorems.Thm_BitDFT_unpackerSpec_rUnary_step
-- name    : BitDFT.unpackerSpec_rUnary_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:55:43.957088+00:00
-- url     : https://prove2.me/theorems/f9b2cd01-b08a-40ae-ad8c-e49db1056e9a
-- title:
--   The unary-scan phase: one transition, with its frame conditions
-- statement:
--   The unpacking machine's second phase consumes the unary prefix of the first header. The theorem records exactly what one of its transitions does, at the level of the symbols the transition is allowed to see.
--
--   Suppose the input head reads a unary mark and the `r`-counter head is not on the end marker. Then the transition leaves the phase unchanged; on the input tape it keeps the scanned symbol and steps the head right; and on the counter tape it writes a mark and steps that head right.
--
--   The second hypothesis is not decoration. A machine in this model may not overwrite the end marker $\triangleright$, and the guard that enforces that rule suppresses any write aimed at a cell holding it. If the counter head is still on cell $0$ when the phase tries to record its first mark, the mark is dropped — which is precisely the defect recorded in `BitDFT.unpackerMachine_counter_blank`. The hypothesis states the condition under which the phase behaves as designed, and it is the condition a leading advance phase has to establish.
--
--   This is the first rung of the machine's run theory: the per-phase transition rule together with its frame conditions, which the inductions over runs of marks consume.
-- source:
--   Internal: per-phase transition rule for Prove2me's BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98), against the machine definition BitDFT_unpackerMachineV2.

import Definitions.Def_BitDFT_unpackerMachineV2

theorem BitDFT.unpackerSpec_rUnary_step (g κ s : Bool) (a : Fin 6 → TMKit.Sym)
    (h : a BitDFT.Unpacker.inT = TMKit.Sym.one)
    (hc0 : a BitDFT.Unpacker.cntR ≠ TMKit.Sym.start) :
    (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.rUnary, g, κ, s⟩ a).1
        = ⟨BitDFT.Unpacker.Ph.rUnary, g, κ, s⟩ ∧
      (BitDFT.Unpacker.guard ⟨BitDFT.Unpacker.Ph.rUnary, g, κ, s⟩ a
          BitDFT.Unpacker.inT).1 = a BitDFT.Unpacker.inT ∧
      (BitDFT.Unpacker.guard ⟨BitDFT.Unpacker.Ph.rUnary, g, κ, s⟩ a
          BitDFT.Unpacker.inT).2 = IntMul.Move.right ∧
      (BitDFT.Unpacker.guard ⟨BitDFT.Unpacker.Ph.rUnary, g, κ, s⟩ a
          BitDFT.Unpacker.cntR).1 = TMKit.Sym.one ∧
      (BitDFT.Unpacker.guard ⟨BitDFT.Unpacker.Ph.rUnary, g, κ, s⟩ a
          BitDFT.Unpacker.cntR).2 = IntMul.Move.right := by sorry
