-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_div_round_up_eq_ceil
-- name    : BitcoinFeerateDiagram.div_round_up_eq_ceil
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:52:53.04036+00:00
-- url     : https://prove2.me/theorems/22be77e4-5dd1-44d9-b6e9-ad4958c1a56c
-- title:
--   Div rounding up is the ceiling
-- statement:
--   For $d > 0$: `div n d false = ⌈n/d⌉`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.div_round_up_eq_ceil (n d : ℤ) (hd : 0 < d) :
    FeeFrac.div n d false = ⌈(n : ℚ) / d⌉ := by sorry
