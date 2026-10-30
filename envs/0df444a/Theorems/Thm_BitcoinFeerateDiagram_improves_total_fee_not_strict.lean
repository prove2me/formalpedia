-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_improves_total_fee_not_strict
-- name    : BitcoinFeerateDiagram.improves_total_fee_not_strict
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:58:50.402125+00:00
-- url     : https://prove2.me/theorems/84ca432b-9dd6-4642-9d47-ced46cc6d3ca
-- title:
--   A strict improvement may keep the total fee
-- statement:
--   There are sorted, positive-size chunkings with `ImprovesFeerateDiagram old new` and equal total fees (one chunk (4, 2) against (3, 1), (1, 1)): the diagram check alone does not make the replacement pay more; `PaysForRBF` does.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.improves_total_fee_not_strict :
    ∃ old new : List FeeFrac, SizesPos old ∧ SizesPos new ∧ FeeratesNonIncreasing old ∧
      FeeratesNonIncreasing new ∧ ImprovesFeerateDiagram old new ∧
      diagramFee old = diagramFee new := by sorry
