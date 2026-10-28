-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_scale_right_ratio_nonneg_lt_one
-- name    : AvramDividend.Classical.chat12_scale_right_ratio_nonneg_lt_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:50:10.162801+00:00
-- url     : https://prove2.me/theorems/e7eac7d5-f874-4b66-b8ca-42250a98c6ed
-- title:
--   Right q-scale ratio lies in the nonnegative unit interval
-- statement:
--   When W(a)≥0, W(a+epsilon)>0 and W(a)<W(a+epsilon), the right scale-function ratio W(a)/W(a+epsilon) belongs to [0,1). This elementary inequality is needed to establish finiteness of the upper renewal geometric budget independently of proving the underlying stochastic exit ratio identity.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic

open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_scale_right_ratio_nonneg_lt_one
    (W : ℝ → ℝ) (a ε : ℝ)
    (hWa : 0 ≤ W a) (hWright : 0 < W (a + ε))
    (hWinc : W a < W (a + ε)) :
    0 ≤ W a / W (a + ε) ∧ W a / W (a + ε) < 1 := by sorry
