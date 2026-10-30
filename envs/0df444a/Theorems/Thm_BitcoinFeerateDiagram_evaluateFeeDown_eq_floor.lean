-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_evaluateFeeDown_eq_floor
-- name    : BitcoinFeerateDiagram.evaluateFeeDown_eq_floor
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:54:35.841353+00:00
-- url     : https://prove2.me/theorems/e721a0fc-b2ef-4296-963d-8639ad821a5d
-- title:
--   EvaluateFeeDown is the floor of fee·size/size, on both code paths
-- statement:
--   For positive size and non-negative `atSize`: `evaluateFeeDown f atSize = ⌊fee · atSize / size⌋`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.evaluateFeeDown_eq_floor (f : FeeFrac) (atSize : ℤ)
    (hs : 0 < f.size) (_ha : 0 ≤ atSize) :
    FeeFrac.evaluateFeeDown f atSize = ⌊((f.fee * atSize : ℤ) : ℚ) / f.size⌋ := by sorry
