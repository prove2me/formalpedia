-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB275_original_fixed_level_product_mass_eq_time_integral_hit_probability
-- name    : AvramDividend.Classical.avram_gbB275_original_fixed_level_product_mass_eq_time_integral_hit_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T22:45:51.894116+00:00
-- url     : https://prove2.me/theorems/5d9507c5-4358-4093-9f13-6dc17336ec2d
-- title:
--   Original fixed-level product occupation equals time integral of hit probabilities
-- statement:
--   Original probability-by-Lebesgue time mass of a finite-horizon fixed-level postpayment reserve hit event equals the physical-time integral of the original hit probability. This is an exact Fubini bridge for the finite-cap zero-jump Gaussian time-grid occupation estimate B274.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB275_original_fixed_level_product_mass_eq_time_integral_hit_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (n : ℕ) :
    (P.prod volume)
      {z : Ω × ℝ |
        0 < z.2 ∧ z.2 < (n : ℝ) ∧
        x + X.X (Real.toNNReal z.2) z.1 -
          rightLimit D (Real.toNNReal z.2) z.1 = b} =
    ∫⁻ t : ℝ, P {ω : Ω |
      0 < t ∧ t < (n : ℝ) ∧
      x + X.X (Real.toNNReal t) ω -
        rightLimit D (Real.toNNReal t) ω = b} ∂volume := by sorry
