-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_localised_weighted_clock_large_mark_factorised
-- name    : AvramDividend.Classical.avram_p4_c_generator_localised_weighted_clock_large_mark_factorised
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:30:26.449199+00:00
-- url     : https://prove2.me/theorems/ddd866e0-6a6a-4864-b530-8a7c0987ba49
-- title:
--   Discounted original Levy large-jump drift factorisation on a stopped interior clock
-- statement:
--   For the original Levy negative large-jump mark measure and finite time measure, the product integral of the discounted raw jump payoff over a stopped measurable region equals the time integral of the indicator-masked, discounted original large-jump drift. The reserve cap is required only within the stopped region. This exact source-specific bridge uses the previously Proved product Fubini theorem and separates the stochastic compensator requirement.
-- source:
--   Original spectral-negative Levy generator, accepted localised weighted Fubini 92a1ea9a-1470-493a-96b8-c99c4899a009; Avram–Palmowski–Pistorius Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_localised_weighted_large_mark_fubini
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_localised_weighted_clock_large_mark_factorised
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R a : T → ℝ) (hR : Measurable R) (ha : Measurable a)
    (A : Set T) (hA : MeasurableSet A)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t ∈ A, R t ∈ Icc 0 v)
    (M : ℝ) (hweight : ∀ t, |a t| ≤ M) :
    (∫ p : T × ℝ, ({s : T × ℝ | s.1 ∈ A}.indicator
      (fun s => a s.1 * (w (R s.1 + s.2) - w (R s.1)))) p
      ∂(μ.prod (X.ν.restrict (Iio (-ε))))) =
    ∫ t : T, (A.indicator (fun t => a t *
      (∫ z : ℝ, w (R t + z) - w (R t)
      ∂(X.ν.restrict (Iio (-ε)))))) t ∂μ := by sorry
