-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a07_original_gaussian_condexp_initial_zero_of_bracket
-- name    : AvramDividend.Classical.avram_a07_original_gaussian_condexp_initial_zero_of_bracket
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:19:34.880693+00:00
-- url     : https://prove2.me/theorems/703cc8b4-e644-422e-b59d-cf68f6e0a2c4
-- title:
--   Original Gaussian residual has zero initial conditional mean at all deterministic times
-- statement:
--   For the original right-continuous filtration, the Gaussian residual martingale with exact quadratic bracket starts from zero almost surely. Consequently its conditional expectation onto the initial sigma-algebra is zero at every deterministic time. This is the source-process initial-event certificate needed before bounded optional stopping.
-- source:
--   Martingale conditional expectation at 0 and zero-time quadratic bracket.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a07_original_gaussian_residual_initial_zero_of_bracket
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a07_original_gaussian_condexp_initial_zero_of_bracket
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (R : ℝ≥0 → Ω → ℝ) (a : ℝ)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      P[R t | 𝓕.rightCont s] =ᵐ[P] R s)
    (hRbracket : ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * a ^ 2) :
    ∀ t : ℝ≥0, P[R t | 𝓕.rightCont 0] =ᵐ[P] (0 : Ω → ℝ) := by sorry
