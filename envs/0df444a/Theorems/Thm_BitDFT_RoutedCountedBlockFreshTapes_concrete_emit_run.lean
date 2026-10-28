-- Prove2me | Theorems.Thm_BitDFT_RoutedCountedBlockFreshTapes_concrete_emit_run
-- name    : BitDFT.RoutedCountedBlockFreshTapes.concrete_emit_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T08:16:37.044108+00:00
-- url     : https://prove2.me/theorems/43e2d7a0-2cdb-4755-a99a-505d91b1e5fa
-- title:
--   Run the serializer from the multiplier product frame
-- statement:
--   Assume the multiplier suffix has placed the product bits on tape 1 with the product head at the first requested output bit, and assume the counted descriptor fits within that product suffix. Then, after the proved handoff into the serializer's emit phase, the serializer completes with the same transition bound as the reusable counted-block run, while preserving all parked multiplier tapes.
-- source:
--   The concrete frame theorem aligns the multiplier's product tape with the serializer input and routes the prior work tapes into their preserved extension slots. The accepted fresh-tape serializer theorem then supplies the complete emission run and its exact time bound. A configuration transport accounts for the serializer continuation's emit entry state.

import Definitions.Def_BitDFT_ConcreteEmitFrame
import Theorems.Thm_BitDFT_routed_counted_block_fresh_tapes_v2
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open IntMul BitDFT.MachineSequence BitDFT.RoutedCountedBlockFreshTapes

theorem BitDFT.RoutedCountedBlockFreshTapes.concrete_emit_run (M : MultitapeTM) (C : Controller (source M))
    (cEnd : C.machine.Cfg)
    (pre out x y : List Bool)
    (hx : val y + 1 ≤ x.length)
    (hProductCells : cEnd.cells ⟨1, by dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ =
      (host M).tapeOf ((pre ++ x).map (host M).bitSym))
    (hProductHead : cEnd.head ⟨1, by dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ =
      pre.length + 1) :
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+2 ∧
      (serializerEmitContinuation M).machine.step^[t]
        (MachineSequence.handoff (suffixControllerOnSerializerHost M C)
          (serializerEmitContinuation M) (suffixEmbed M C
            (fun j p => if j.val < (source M).k then (source M).blank else
              (emitFrame M (emitHostBase M cEnd) (parkedCells M cEnd.cells) (parkedHeads M cEnd.head)
                pre out x y).cells j p)
            (fun j => if j.val < (source M).k then 0 else
              (emitFrame M (emitHostBase M cEnd) (parkedCells M cEnd.cells) (parkedHeads M cEnd.head)
                pre out x y).head j) cEnd)) =
      castSerializerCfg M (embed M (emitHostBase M cEnd) (parkedCells M cEnd.cells) (parkedHeads M cEnd.head)
        (AlphabetEmbedding.embed
          (CountedBlockOnMultiplierAlphabet.alphabetMap (source M))
          (CountedBlock.frame pre out x y y.reverse (val y+1) .halt))) := by sorry
