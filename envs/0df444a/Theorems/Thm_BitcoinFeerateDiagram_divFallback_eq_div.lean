-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_divFallback_eq_div
-- name    : BitcoinFeerateDiagram.divFallback_eq_div
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:54:13.228048+00:00
-- url     : https://prove2.me/theorems/b8b6b640-787c-4d12-9a0c-b181a71f9248
-- title:
--   The split division agrees with Div
-- statement:
--   For $d > 0$: `divFallback (h, l) d rd = div (h · 2^32 + l) d rd`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.divFallback_eq_div (n : ℤ × ℤ) (d : ℤ) (hd : 0 < d) (rd : Bool) :
    FeeFrac.divFallback n d rd = FeeFrac.div (n.1 * 2 ^ 32 + n.2) d rd := by sorry
