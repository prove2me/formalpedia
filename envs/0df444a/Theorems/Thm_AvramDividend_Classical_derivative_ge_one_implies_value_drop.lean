-- Prove2me | Theorems.Thm_AvramDividend_Classical_derivative_ge_one_implies_value_drop
-- name    : AvramDividend.Classical.derivative_ge_one_implies_value_drop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:14:00.410398+00:00
-- url     : https://prove2.me/theorems/7e6a3503-e9b1-4bd9-a4b9-f5f21e29b242
-- title:
--   Marginal value derivative at least one forces full dividend payment to be covered by value drop
-- statement:
--   For any continuous w on [a,b] that is differentiable on (a,b) and satisfies w'(z)≥1 throughout the open interval, paying a dividend of b−a reduces w by at least the amount paid: b−a≤w(b)−w(a). Prove using monotonicity of w(z)−z and Mathlib's monotoneOn_of_deriv_nonneg. This is the generic HJB dividend-gradient verification step, without restricting to exponential test functions.
-- source:
--   Pinned Mathlib Analysis.Calculus.Deriv.MeanValue monotoneOn_of_deriv_nonneg and deriv_sub.

import Mathlib
open Set

theorem AvramDividend.Classical.derivative_ge_one_implies_value_drop
    (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn w (Icc a b))
    (hdiff : DifferentiableOn ℝ w (Ioo a b))
    (hgrad : ∀ z ∈ Ioo a b, 1 ≤ deriv w z) :
    b - a ≤ w b - w a := by sorry
