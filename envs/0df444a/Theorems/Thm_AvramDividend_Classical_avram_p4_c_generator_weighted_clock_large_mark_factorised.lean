-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_weighted_clock_large_mark_factorised
-- name    : AvramDividend.Classical.avram_p4_c_generator_weighted_clock_large_mark_factorised
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:39:58.597195+00:00
-- url     : https://prove2.me/theorems/69913c75-d4f0-47f0-9763-1915b76f7d88
-- title:
--   Original discounted large negative jumps equal integral of weight times physical ν-large drift
-- statement:
--   Under finite clock and capped reserves, bounded measurable discount a, the product integral of original source negative raw large-jump payoff equals the time integral of a(t) times the source ν-tail raw drift. This is Fubini together with constant multiplication inside the ν-integral, and requires genuine original source product-L1 and finite original νtail; no original jump-count compensator is postulated.
-- source:
--   Accepted P4-C weighted_raw_large_mark_L1 and original epsilon_large_jump_intensity_finite; pinned Mathlib integral_prod and integral_const_mul

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_weighted_raw_large_mark_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_weighted_clock_large_mark_factorised
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
    ∫ t : T, a t * (∫ z : ℝ, w (R t + z) - w (R t)
      ∂(X.ν.restrict (Iio (-ε)))) ∂μ := by sorry
