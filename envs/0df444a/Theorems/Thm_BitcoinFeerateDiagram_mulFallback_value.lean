-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_mulFallback_value
-- name    : BitcoinFeerateDiagram.mulFallback_value
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:53:38.798732+00:00
-- url     : https://prove2.me/theorems/562887a1-2186-48d1-a91f-29e2f4a64854
-- title:
--   The split multiplication computes the product
-- statement:
--   `(mulFallback a b).1 · 2^32 + (mulFallback a b).2 = a · b`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.mulFallback_value (a b : ℤ) :
    (FeeFrac.mulFallback a b).1 * 2 ^ 32 + (FeeFrac.mulFallback a b).2 = FeeFrac.mul a b := by sorry
