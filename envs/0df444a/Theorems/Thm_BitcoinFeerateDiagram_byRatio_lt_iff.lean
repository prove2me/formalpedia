-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_byRatio_lt_iff
-- name    : BitcoinFeerateDiagram.byRatio_lt_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:51:46.827492+00:00
-- url     : https://prove2.me/theorems/cab6e413-7b59-43a7-a16b-364bc52fbb14
-- title:
--   ByRatio less-than is the rational less-than
-- statement:
--   For positive sizes: `byRatioCmp a b = .lt ↔ ratio a < ratio b`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.byRatio_lt_iff (a b : FeeFrac) (ha : 0 < a.size) (hb : 0 < b.size) :
    FeeFrac.byRatioCmp a b = .lt ↔ a.ratio < b.ratio := by sorry
