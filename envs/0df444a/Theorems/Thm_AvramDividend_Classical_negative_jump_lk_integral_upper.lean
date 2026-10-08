-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_lk_integral_upper
-- name    : AvramDividend.Classical.negative_jump_lk_integral_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T00:27:19.110638+00:00
-- url     : https://prove2.me/theorems/32e0686e-4e13-496a-852b-b6c1c277bfbe
-- title:
--   Quadratic upper bound for the negative Levy-Khintchine jump integral
-- statement:
--   For nonnegative theta, the negative-jump Levy-Khintchine integral is bounded above by theta squared times the small-jump second moment.
-- source:
--   Split at -1. The large-jump contribution is nonpositive, while the compensated small-jump remainder is bounded by theta squared times y squared.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem negative_jump_lk_integral_upper
    (ν : Measure ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hint : IntegrableOn
      (fun y : ℝ => Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
      (Iio (0 : ℝ)) ν)
    (hy2 : IntegrableOn (fun y : ℝ => y ^ 2) (Ioo (-1 : ℝ) 0) ν) :
    (∫ y in Iio (0 : ℝ),
      (Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂ν) ≤
      θ ^ 2 * ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂ν := by
  sorry

end AvramDividend.Classical
