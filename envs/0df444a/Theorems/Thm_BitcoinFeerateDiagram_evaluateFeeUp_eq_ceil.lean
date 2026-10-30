-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_evaluateFeeUp_eq_ceil
-- name    : BitcoinFeerateDiagram.evaluateFeeUp_eq_ceil
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:55:01.384497+00:00
-- url     : https://prove2.me/theorems/e7f0992b-49ad-4136-8223-9bfcf82eca46
-- title:
--   EvaluateFeeUp is the ceiling, on both code paths
-- statement:
--   As above with the ceiling.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.evaluateFeeUp_eq_ceil (f : FeeFrac) (atSize : ℤ)
    (hs : 0 < f.size) (_ha : 0 ≤ atSize) :
    FeeFrac.evaluateFeeUp f atSize = ⌈((f.fee * atSize : ℤ) : ℚ) / f.size⌉ := by sorry
