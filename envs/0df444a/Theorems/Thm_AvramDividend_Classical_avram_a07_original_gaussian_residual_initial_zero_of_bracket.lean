-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a07_original_gaussian_residual_initial_zero_of_bracket
-- name    : AvramDividend.Classical.avram_a07_original_gaussian_residual_initial_zero_of_bracket
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:56:28.397497+00:00
-- url     : https://prove2.me/theorems/661e0848-f07c-460f-b705-78735af42e99
-- title:
--   Original Gaussian residual starts at zero from its exact quadratic bracket
-- statement:
--   The exact original Gaussian-residual second moment formula at every deterministic time implies that the residual vanishes almost surely at time zero. This normalises the Gaussian martingale term for the unbounded-variation stopped Ito-Meyer cash ledger.
-- source:
--   Nonnegative integral zero and quadratic-moment identity at t=0.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a07_original_gaussian_residual_initial_zero_of_bracket
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (R : ℝ≥0 → Ω → ℝ) (a : ℝ)
    (hRbracket : ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * a ^ 2) :
    ∀ᵐ ω ∂P, R 0 ω = 0 := by sorry
