-- Prove2me | Theorems.Thm_BitDFT_routed_counted_block_fresh_tapes_v2
-- name    : BitDFT.routed_counted_block_fresh_tapes_v2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T06:37:12.471693+00:00
-- url     : https://prove2.me/theorems/8a288b22-da75-443d-aee0-621a6d67a1b7
-- title:
--   Counted-block serialization on fresh tapes preserves the multiplier frame
-- statement:
--   For any multiplier alphabet, any parked host frame, and any descriptor whose length does not exceed the product source length, the counted-block serializer can run with its output, countdown, and template on three appended tapes while preserving the host frame. The source remains on tape 1, all original tapes remain represented in the routed configuration, and the run takes at most 6(|y|+1)+4|y|+2 transitions.
-- source:
--   First use the accepted counted-block run in the embedded multiplier alphabet. The accepted exact-run theorem for tape extension lifts this run while preserving arbitrary caller data. The fresh-tape permutation then routes the serializer's output and two descriptor tapes to the appended positions, and the accepted permutation simulation preserves the exact transition count.

import Definitions.Def_BitDFT_RoutedCountedBlockFreshTapes
import Theorems.Thm_BitDFT_counted_block_correct
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_permutation_run
import Mathlib.Tactic
set_option autoImplicit false
open IntMul BitDFT.RoutedCountedBlockFreshTapes

theorem BitDFT.routed_counted_block_fresh_tapes_v2 (M : MultitapeTM)
    (base : (host M).Cfg)
    (extraCells : Fin (extension M).k → ℕ → (source M).Sym)
    (extraHeads : Fin (extension M).k → ℕ)
    (pre out x y : List Bool) (hx : val y + 1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+2 ∧
      (machine M).step^[t]
        (embed M base extraCells extraHeads
          (AlphabetEmbedding.embed
            (CountedBlockOnMultiplierAlphabet.alphabetMap (source M))
            (CountedBlock.frame pre out x y y.reverse 0 .emit))) =
      embed M base extraCells extraHeads
        (AlphabetEmbedding.embed
          (CountedBlockOnMultiplierAlphabet.alphabetMap (source M))
          (CountedBlock.frame pre out x y y.reverse (val y+1) .halt)) := by sorry
