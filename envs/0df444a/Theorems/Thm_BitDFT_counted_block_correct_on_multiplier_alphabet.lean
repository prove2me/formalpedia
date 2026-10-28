-- Prove2me | Theorems.Thm_BitDFT_counted_block_correct_on_multiplier_alphabet
-- name    : BitDFT.counted_block_correct_on_multiplier_alphabet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T04:47:56.716432+00:00
-- url     : https://prove2.me/theorems/a3e76942-1b81-42b5-8001-e2727465eb49
-- title:
--   Counted-block run in the multiplier alphabet
-- statement:
--   For any multiplier alphabet and caller frame, when the counted-block source has at least val(y)+1 bits, its serializer run can be performed on four designated work tapes using the multiplier's symbols. The call preserves the host input tape and all caller data parked outside those four work tapes, and takes at most 6(val(y)+1)+4|y|+2 transitions.
-- source:
--   The proof composes the accepted counted-block run with the accepted alphabet-embedding simulation, then uses the exact work-tape relocation run theorem.

import Definitions.Def_BitDFT_CountedBlockOnMultiplierAlphabet
import Theorems.Thm_BitDFT_counted_block_correct
import Theorems.Thm_BitDFT_alphabet_embedding_correct
set_option autoImplicit false
open IntMul

theorem BitDFT.counted_block_correct_on_multiplier_alphabet
    (M : MultitapeTM)
    (base : (BitDFT.CountedBlockOnMultiplierAlphabet.machine M).Cfg)
    (pre out x y : List Bool) (hx : val y + 1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(val y+1)+4*y.length+2 ∧
      (BitDFT.CountedBlockOnMultiplierAlphabet.machine M).step^[t]
        (BitDFT.CountedBlockOnMultiplierAlphabet.embed M base
          (BitDFT.AlphabetEmbedding.embed
            (BitDFT.CountedBlockOnMultiplierAlphabet.alphabetMap M)
            (BitDFT.CountedBlock.frame pre out x y y.reverse 0 .emit))) =
      BitDFT.CountedBlockOnMultiplierAlphabet.embed M base
        (BitDFT.AlphabetEmbedding.embed
          (BitDFT.CountedBlockOnMultiplierAlphabet.alphabetMap M)
          (BitDFT.CountedBlock.frame pre out x y y.reverse (val y+1) .halt)) := by sorry
