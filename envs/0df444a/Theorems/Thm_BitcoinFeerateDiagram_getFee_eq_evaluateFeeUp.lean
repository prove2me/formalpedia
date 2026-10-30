-- Prove2me | Theorems.Thm_BitcoinFeerateDiagram_getFee_eq_evaluateFeeUp
-- name    : BitcoinFeerateDiagram.getFee_eq_evaluateFeeUp
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:55:45.313159+00:00
-- url     : https://prove2.me/theorems/7f46b840-1e02-4f4c-97e1-5c3c9f74b887
-- title:
--   The replacement mission's GetFee is EvaluateFeeUp
-- statement:
--   `r.getFee v = evaluateFeeUp ⟨r.fee, r.size⟩ v`, linking the two missions' fee arithmetic.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.getFee_eq_evaluateFeeUp (r : FeeRate) (v : ℕ) :
    (r.getFee v : ℤ) = FeeFrac.evaluateFeeUp ⟨r.fee, r.size⟩ v := by sorry
