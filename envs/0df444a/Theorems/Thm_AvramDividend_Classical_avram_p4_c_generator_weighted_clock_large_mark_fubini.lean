-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_weighted_clock_large_mark_fubini
-- name    : AvramDividend.Classical.avram_p4_c_generator_weighted_clock_large_mark_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:29:53.05389+00:00
-- url     : https://prove2.me/theorems/72bf0129-ada9-4d34-a0f9-9efda100ba12
-- title:
--   Fubini identity for discounted original large negative jump payoff under finite clock and bounded reserves
-- statement:
--   For original spectrally-negative Levy jump law, bounded discount weight and globally capped measurable reserves on finite clock, the integral of a times raw negative large-jump payoff against μ product original νtail equals the iterated time and jump integral. The product integrability is supplied by an accepted source-specific helper and the restricted original ν has finite mass.
-- source:
--   Accepted P4-C avram_p4_c_generator_weighted_raw_large_mark_L1 (7fd71577-0f92-47b1-a1a4-7ac1c6f08a48), epsilon_large_jump_intensity_finite (23f951a3-7c41-4e79-b5b4-7c8c2e9c7ca6); pinned Mathlib integral_prod.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_weighted_raw_large_mark_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_weighted_clock_large_mark_fubini
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R a : T → ℝ) (hR : Measurable R) (ha : Measurable a)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t, R t ∈ Icc 0 v)
    (M : ℝ) (hweight : ∀ t, |a t| ≤ M) :
    (∫ p : T × ℝ, a p.1 * (w (R p.1 + p.2) - w (R p.1))
      ∂(μ.prod (X.ν.restrict (Iio (-ε))))) =
    ∫ t : T, ∫ z : ℝ, a t * (w (R t + z) - w (R t))
      ∂(X.ν.restrict (Iio (-ε))) ∂μ := by sorry
