-- Prove2me | Theorems.Thm_BitDFT_tracked_call_emit_serializer
-- name    : BitDFT.tracked_call_emit_serializer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T08:38:41.170907+00:00
-- url     : https://prove2.me/theorems/c4de9691-960f-4454-8683-80711092633e
-- title:
--   Serialize an actual tracked multiplier result
-- statement:
--   Suppose a tracked multiplier call returns a product word, and a preserved caller tape supplies a binary counter segment of length L followed by a non-bit sentinel. After normalizing the product, the accepted rewind-and-advance controller positions its head at cell L+1. If the requested counted descriptor fits in the remaining product suffix, the routed serializer then emits that suffix from the actual returned multiplier frame, preserving the caller tapes and satisfying the serializer's transition bound.
-- source:
--   The first phase is the accepted exact run from the tracked multiplier return through output normalization, rewind, and bit-counted head positioning. The output tape of the tracked shift machine is proved to be the product word, so splitting it at L supplies the serializer's prefix, remaining source, and required head position. The accepted concrete emit-frame and serializer-run results then finish the serialization.

import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_IntMul_TrackedOutputShift
import Definitions.Def_BitDFT_BitAdvance
import Definitions.Def_BitDFT_RewindTape
import Definitions.Def_BitDFT_MachineSequence
import Definitions.Def_BitDFT_LiftController
import Definitions.Def_BitDFT_ConcreteEmitFrame
import Theorems.Thm_BitDFT_routed_counted_block_fresh_tapes_v2
import Theorems.Thm_BitDFT_tracked_call_product_suffix
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open IntMul BitDFT BitDFT.MachineSequence BitDFT.RoutedCountedBlockFreshTapes

theorem BitDFT.tracked_call_emit_serializer (M : MultitapeTM)
    (base : (TrackedBankedCall.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (productWord : List Bool)
    (counter : Fin (TrackedOutputShift.machine M).k)
    (hcounterProduct : counter ≠ ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩)
    (counterHead p L : ℕ) (hp : p = productWord.length + 1)
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
        (counterHead+L) ≠ (TrackedOutputShift.machine M).one)
    (hL : L ≤ productWord.length) (out y : List Bool)
    (hfit : val y + 1 ≤ (productWord.drop L).length) :
    let product : Fin (TrackedOutputShift.machine M).k :=
      ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩
    let callFrame := TrackedBankedCall.finalFrame M base 1 offset extent c productWord
    let shiftStart : (TrackedOutputShift.machine M).Cfg :=
      ⟨.rewind, callFrame.cells, callFrame.head⟩
    let shifted := TrackedOutputShift.finalFrame M shiftStart productWord
    let P := MachineSequence.native (TrackedOutputShift.machine M)
    let Q := RewindTape.control P.machine product
    let R := BitAdvance.control P.machine product counter (Ne.symm hcounterProduct)
    let V := MachineSequence.sequence Q R
    let Vflat := MachineSequence.liftController P V
    let C := MachineSequence.sequence P Vflat
    let cEnd := MachineSequence.rightCfg P Vflat
      (MachineSequence.rightCfg Q R
        (BitAdvance.frame P.machine product counter (Ne.symm hcounterProduct)
          shifted true (L+1) (counterHead+L)))
    ∃ ts tr : ℕ,
      ts ≤ 4*productWord.length+4+(p+L+3)+1 ∧
      tr ≤ 6*(val y+1)+4*y.length+2 ∧
      C.machine.step^[ts] (MachineSequence.leftCfg P Vflat shiftStart) = cEnd ∧
      (serializerEmitContinuation M).machine.step^[tr]
        (MachineSequence.handoff (suffixControllerOnSerializerHost M C)
          (serializerEmitContinuation M) (suffixEmbed M C
            (fun j q => if j.val < (source M).k then (source M).blank else
              (emitFrame M (emitHostBase M cEnd) (parkedCells M cEnd.cells)
                (parkedHeads M cEnd.head) (productWord.take L) out
                (productWord.drop L) y).cells j q)
            (fun j => if j.val < (source M).k then 0 else
              (emitFrame M (emitHostBase M cEnd) (parkedCells M cEnd.cells)
                (parkedHeads M cEnd.head) (productWord.take L) out
                (productWord.drop L) y).head j) cEnd)) =
      castSerializerCfg M (embed M (emitHostBase M cEnd)
        (parkedCells M cEnd.cells) (parkedHeads M cEnd.head)
        (AlphabetEmbedding.embed
          (CountedBlockOnMultiplierAlphabet.alphabetMap (source M))
          (CountedBlock.frame (productWord.take L) out (productWord.drop L) y
            y.reverse (val y+1) .halt))) := by sorry
