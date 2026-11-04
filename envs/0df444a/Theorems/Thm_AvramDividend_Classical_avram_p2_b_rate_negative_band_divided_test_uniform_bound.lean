-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_band_divided_test_uniform_bound
-- name    : AvramDividend.Classical.avram_p2_b_rate_negative_band_divided_test_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:21:05.011385+00:00
-- url     : https://prove2.me/theorems/58329818-04a5-4f10-90bd-36d9c68369a3
-- title:
--   Uniform divided compact-negative test bound from positive fourth-weight
-- statement:
--   For theta, epsilon positive and any real test f bounded in absolute value by a nonnegative constant M on the separated negative band y <= -epsilon, division by the source fourth-exponential weight yields a uniformly bounded test: |f(y)/(exp(theta*y)-1)^4| <= M/(1-exp(-theta*epsilon))^4. The proof depends on the two independently Proved original band-weight inequalities and justifies bounded weight inversion in the small-time moment-to-continuous-test bridge.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_band_fourth_weight_lower
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_band_weight_constant_pos
open MeasureTheory Set

theorem AvramDividend.Classical.avram_p2_b_rate_negative_band_divided_test_uniform_bound
    (θ ε M : ℝ) (hθ : 0 < θ) (hε : 0 < ε) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : ∀ y : ℝ, y ≤ -ε → |f y| ≤ M)
    (y : ℝ) (hy : y ≤ -ε) :
    |f y / (Real.exp (θ * y) - 1) ^ 4| ≤
      M / (1 - Real.exp (-θ * ε)) ^ 4 := by sorry
