-- Prove2me | Theorems.Thm_BitDFT_tracked_call_product_suffix
-- name    : BitDFT.tracked_call_product_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T06:06:25.910986+00:00
-- url     : https://prove2.me/theorems/b7be85e0-a877-4435-98e3-7489b8580878
-- title:
--   Position a tracked multiplier result at the serializer suffix
-- statement:
--   Let a tracked integer-multiplier call return a product word on its output bank. Assume a distinct caller tape contains the L-bit binary counter segment and a non-bit sentinel, while the product bank retains its rewind marker. After the fixed output normalizer runs, a fixed controller rewinds the product bank and advances it across those L counter bits. The complete multitape configuration then has its product head at cell L+1, the first cell of the low-order suffix, with every other tape preserved. The combined run uses at most 4|w|+4+p+L+4 transitions, where w is the returned product word and p=|w|+1 is its normalized head position.
-- source:
--   Composes the accepted tracked-call output-normalization run with the proved rewind, bit-advance, controller-lifting, and sequencing theorems. It connects the actual multiplier caller frame to the exact product-head position required by counted-block serialization; it does not assert descriptor staging or the repeated coordinate loop.

import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_IntMul_TrackedOutputShift
import Definitions.Def_BitDFT_RewindTape
import Definitions.Def_BitDFT_BitAdvance
import Definitions.Def_BitDFT_MachineSequence
import Definitions.Def_BitDFT_LiftController
import Theorems.Thm_BitDFT_banked_call_output_shift
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_BitAdvance_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Mathlib.Tactic
open IntMul BitDFT BitDFT.MachineSequence

theorem BitDFT.tracked_call_product_suffix (M : MultitapeTM)
    (base : (TrackedBankedCall.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (productWord : List Bool)
    (counter : Fin (TrackedOutputShift.machine M).k)
    (hcounterProduct : counter ≠ ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩)
    (counterHead p L : ℕ)
    (hp : p = productWord.length + 1)
    (hcounterHead :
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).head counter = counterHead)
    (hmarker :
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).cells
        ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩ 0 =
          (TrackedOutputShift.machine M).startSym)
    (hbits : ∀ r, r < L →
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).cells counter
        (counterHead+r) = (TrackedOutputShift.machine M).zero ∨
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).cells counter
        (counterHead+r) = (TrackedOutputShift.machine M).one)
    (hstop :
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).cells counter
        (counterHead+L) ≠ (TrackedOutputShift.machine M).zero ∧
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).cells counter
        (counterHead+L) ≠ (TrackedOutputShift.machine M).one) :
    ∃ t : ℕ, t ≤ 4*productWord.length+4 + (p+L+3) + 1 ∧
      let callFrame := TrackedBankedCall.finalFrame M base 1 offset extent c productWord
      let shiftStart : (TrackedOutputShift.machine M).Cfg :=
        ⟨.rewind, callFrame.cells, callFrame.head⟩
      let shifted := TrackedOutputShift.finalFrame M shiftStart productWord
      let P := MachineSequence.native (TrackedOutputShift.machine M)
      let Q := RewindTape.control P.machine ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩
      let R := BitAdvance.control P.machine ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩
        counter (Ne.symm hcounterProduct)
      let V := MachineSequence.sequence Q R
      let Vflat := MachineSequence.liftController P V
      (MachineSequence.sequence P Vflat).machine.step^[t]
        (MachineSequence.leftCfg P Vflat shiftStart) =
      MachineSequence.rightCfg P Vflat
        (MachineSequence.rightCfg Q R
          (BitAdvance.frame P.machine ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩
            counter (Ne.symm hcounterProduct) shifted true (L+1) (counterHead+L))) := by sorry
