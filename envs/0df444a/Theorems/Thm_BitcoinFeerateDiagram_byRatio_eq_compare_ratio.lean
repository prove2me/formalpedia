-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_byRatio_eq_compare_ratio
-- name    : BitcoinFeerateDiagram.byRatio_eq_compare_ratio
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:51:09.227786+00:00
-- url     : https://prove2.me/theorems/ad0cb6da-cbcf-4a31-87a8-e03a7dc7852f
-- title:
--   Core's cross-multiplied fee-rate comparison is the comparison of exact ratios
-- statement:
--   For positive sizes: `byRatioCmp a b = compare (ratio a) (ratio b)`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.byRatio_eq_compare_ratio (a b : FeeFrac)
    (ha : 0 < a.size) (hb : 0 < b.size) :
    FeeFrac.byRatioCmp a b = compare a.ratio b.ratio := by sorry
