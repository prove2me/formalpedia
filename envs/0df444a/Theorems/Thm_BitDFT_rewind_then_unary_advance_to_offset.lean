-- Prove2me | Theorems.Thm_BitDFT_rewind_then_unary_advance_to_offset
-- name    : BitDFT.rewind_then_unary_advance_to_offset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T04:56:02.119991+00:00
-- url     : https://prove2.me/theorems/e70b86a7-1950-4d7c-9220-072a77aface4
-- title:
--   Rewind and advance to a unary-counted offset
-- statement:
--   Let a source tape contain the rewind marker at cell 0 and no further marker at positive cells. Let a distinct counter tape contain L consecutive one symbols from its current head, followed by a non-one symbol. Starting with the rewind controller positioned p cells to the right of the marker, first rewind the source head to cell 1 and then advance it by the unary count L. The composed controller reaches the exact offset frame in at most p+L+3 transitions.
-- source:
--   This exact frame-and-time theorem composes the accepted rewind and unary-advance controllers. It supplies the head-positioning step needed before invoking the counted-block serializer on the low-width suffix of a multiplier product.

import Definitions.Def_BitDFT_RewindTape
import Definitions.Def_BitDFT_UnaryAdvance
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_UnaryAdvance_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
set_option autoImplicit false
open IntMul BitDFT.MachineSequence

theorem BitDFT.rewind_then_unary_advance_to_offset
    (N : MultitapeTM) (source counter : Fin N.k) (hsc : source ≠ counter)
    (base : N.Cfg) (p L : ℕ)
    (hmarker : base.cells source 0 = N.startSym)
    (hsource : ∀ r, 0 < r → base.cells source r ≠ N.startSym)
    (hones : ∀ r, r < L → base.cells counter (base.head counter+r) = N.one)
    (hstop : base.cells counter (base.head counter+L) ≠ N.one) :
    ∃ t : ℕ, t ≤ p + L + 3 ∧
      (MachineSequence.sequence (BitDFT.RewindTape.control N source)
        (BitDFT.UnaryAdvance.control N source counter hsc)).machine.step^[t]
        (MachineSequence.leftCfg (BitDFT.RewindTape.control N source)
          (BitDFT.UnaryAdvance.control N source counter hsc)
          (BitDFT.RewindTape.frame N source base false p)) =
      MachineSequence.rightCfg (BitDFT.RewindTape.control N source)
        (BitDFT.UnaryAdvance.control N source counter hsc)
        (BitDFT.UnaryAdvance.frame N source counter hsc base true (L+1)
          (base.head counter+L)) := by sorry
