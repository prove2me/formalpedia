-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_div_round_down_eq_floor
-- name    : BitcoinFeerateDiagram.div_round_down_eq_floor
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:52:16.059415+00:00
-- url     : https://prove2.me/theorems/f179d156-5a6e-4427-b3b5-7159f760079c
-- title:
--   Div rounding down is the floor
-- statement:
--   For $d > 0$: `div n d true = ⌊n/d⌋`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.div_round_down_eq_floor (n d : ℤ) (hd : 0 < d) :
    FeeFrac.div n d true = ⌊(n : ℚ) / d⌋ := by sorry
