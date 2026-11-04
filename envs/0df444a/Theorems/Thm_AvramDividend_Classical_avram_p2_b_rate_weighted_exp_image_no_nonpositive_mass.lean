-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_exp_image_no_nonpositive_mass
-- name    : AvramDividend.Classical.avram_p2_b_rate_weighted_exp_image_no_nonpositive_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:40:28.618914+00:00
-- url     : https://prove2.me/theorems/7b1f779c-d480-4e79-8113-a697e246b1f0
-- title:
--   All nonpositive image mass vanishes for any weighted exponential pushforward
-- statement:
--   For any measurable real random variable and any nonnegative density weight, its weighted exponential pushforward measure puts zero mass on (-infinity,0]. This deterministic measure-theoretic lemma establishes the crucial nonnegative-support premise for the actual rescaled weighted original Lévy exp(X_h) image, so controlling only its positive right tail gives full tightness.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_weighted_exp_image_no_nonpositive_mass
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (w : Ω → ℝ≥0∞) :
    ((μ.withDensity w).map (fun ω => Real.exp (Y ω))) (Iic (0 : ℝ)) = 0 := by sorry
