-- Prove2me | Theorems.Thm_BitDFT_rewind_then_bit_advance_to_offset
-- name    : BitDFT.rewind_then_bit_advance_to_offset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T05:05:07.374213+00:00
-- url     : https://prove2.me/theorems/6c614a2e-5d47-4b05-baa8-e5091fae4356
-- title:
--   Rewind and advance across a binary suffix
-- statement:
--   Let a source head start p cells to the right of its unique rewind marker, and let a distinct counter tape start with L binary symbols followed by a non-binary symbol. Rewind the source to cell 1, then advance both source and counter heads across those L binary symbols. The exact resulting frame is reached in at most p+L+3 transitions, with all tape contents preserved.
-- source:
--   This composes the accepted rewind and binary-advance controllers. It uses a q-bit multiplier operand as the counter for the remaining suffix length, avoiding a separate unary counter tape.

import Definitions.Def_BitDFT_RewindTape
import Definitions.Def_BitDFT_BitAdvance
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_BitAdvance_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
set_option autoImplicit false
open IntMul BitDFT BitDFT.MachineSequence

theorem BitDFT.rewind_then_bit_advance_to_offset
    (N : MultitapeTM) (source counter : Fin N.k) (hsc : source ≠ counter)
    (base : N.Cfg) (p L counterHead : ℕ)
    (hcounter : base.head counter = counterHead)
    (hmarker : base.cells source 0 = N.startSym)
    (hsource : ∀ r, 0 < r → base.cells source r ≠ N.startSym)
    (hbits : ∀ r, r < L →
      base.cells counter (counterHead+r) = N.zero ∨ base.cells counter (counterHead+r) = N.one)
    (hstop : base.cells counter (counterHead+L) ≠ N.zero ∧
      base.cells counter (counterHead+L) ≠ N.one) :
    ∃ t : ℕ, t ≤ p + L + 3 ∧
      (MachineSequence.sequence (BitDFT.RewindTape.control N source)
        (BitDFT.BitAdvance.control N source counter hsc)).machine.step^[t]
        (MachineSequence.leftCfg (BitDFT.RewindTape.control N source)
          (BitDFT.BitAdvance.control N source counter hsc)
          (BitDFT.RewindTape.frame N source base false p)) =
      MachineSequence.rightCfg (BitDFT.RewindTape.control N source)
        (BitDFT.BitAdvance.control N source counter hsc)
        (BitDFT.BitAdvance.frame N source counter hsc base true (L+1)
          (counterHead+L)) := by sorry
