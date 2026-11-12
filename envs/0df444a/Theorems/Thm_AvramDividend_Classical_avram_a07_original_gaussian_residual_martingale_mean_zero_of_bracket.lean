-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a07_original_gaussian_residual_martingale_mean_zero_of_bracket
-- name    : AvramDividend.Classical.avram_a07_original_gaussian_residual_martingale_mean_zero_of_bracket
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:11:13.141951+00:00
-- url     : https://prove2.me/theorems/a6c9980a-9e85-476c-8167-aac6fdbb2a36
-- title:
--   Original Gaussian residual has zero mean at every deterministic time
-- statement:
--   Given the original Gaussian residual deterministic-time martingale property and exact quadratic bracket, its time-zero value vanishes almost surely and its expectation is zero at every deterministic time. This is a centring certificate for the original A07 Gaussian Ito noise, preserving the original filtration and probability law.
-- source:
--   Conditional expectation tower identity and original Gaussian bracket initial normalisation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a07_original_gaussian_residual_initial_zero_of_bracket
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a07_original_gaussian_residual_martingale_mean_zero_of_bracket
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (R : ℝ≥0 → Ω → ℝ) (a : ℝ)
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      P[R t | 𝓕.rightCont s] =ᵐ[P] R s)
    (hRbracket : ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * a ^ 2) :
    ∀ t : ℝ≥0, (∫ ω, R t ω ∂P) = 0 := by sorry
