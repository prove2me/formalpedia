-- Prove2me | Theorems.Thm_BitDFT_rewind_then_grouped_unary_v2
-- name    : BitDFT.rewind_then_grouped_unary_v2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T05:43:26.264997+00:00
-- url     : https://prove2.me/theorems/a137c5fe-6533-4746-b315-f3c2508dc762
-- title:
--   Rewind and position using the grouped unary controller
-- statement:
--   Suppose a designated counter tape has a start marker at cell $0$, no other start markers, exactly $3r+5$ consecutive one symbols beginning at cell $1$, and then a non-one symbol. If the source head is at its specified position, the composed controller first rewinds the counter to its first mark, then runs the grouped unary positioning controller. It reaches the exact final configuration with the source head advanced by $r+1$ cells and the counter head at the sentinel. The run uses at most $6r+14$ transitions, including the single controller handoff.
-- source:
--   Composition of the accepted rewind_tape_correct and GroupedUnaryAdvance.correct results through the accepted exact machine-sequence theorem. This prepares the operand head from the logarithmic scanner output; it is a component of the rescaling machine, not the complete coordinate scaler.

import Definitions.Def_BitDFT_GroupedUnaryAdvance
import Definitions.Def_BitDFT_RewindTape
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Mathlib.Tactic
open IntMul BitDFT.MachineSequence

theorem BitDFT.rewind_then_grouped_unary_v2
    (N : MultitapeTM) (source counter : Fin N.k) (hsc : source ≠ counter)
    (base : N.Cfg) (r sourceHead : ℕ)
    (hsourcehead : base.head source = sourceHead)
    (hmarker : base.cells counter 0 = N.startSym)
    (hsource : ∀ p, 0 < p → base.cells counter p ≠ N.startSym)
    (hones : ∀ j, j < 3*r+5 → base.cells counter (1+j) = N.one)
    (hstop : base.cells counter (1+3*r+5) ≠ N.one) :
    ∃ t ≤ (3*r+5)+1+1+(3*r+6),
      (BitDFT.MachineSequence.sequence
        (BitDFT.RewindTape.control N counter)
        (BitDFT.GroupedUnaryAdvance.control N source counter hsc)).machine.step^[t]
        (BitDFT.MachineSequence.leftCfg
          (BitDFT.RewindTape.control N counter)
          (BitDFT.GroupedUnaryAdvance.control N source counter hsc)
          (BitDFT.RewindTape.frame N counter base false (3*r+5))) =
      BitDFT.MachineSequence.rightCfg
        (BitDFT.RewindTape.control N counter)
        (BitDFT.GroupedUnaryAdvance.control N source counter hsc)
        (BitDFT.GroupedUnaryAdvance.frame N source counter hsc base .halt
          (sourceHead+r+1) (1+3*r+5)) := by sorry
