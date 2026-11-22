-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_clipped_gaussian_active_mask_stoppingSigma
-- name    : AvramDividend.Classical.avram_a24_original_clipped_gaussian_active_mask_stoppingSigma
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T18:14:40.192869+00:00
-- url     : https://prove2.me/theorems/6943b08f-881b-4a2b-8b27-2ec660fe3fa0
-- title:
--   Clipped physical Gaussian active-cell event measurable in the stopped sigma-algebra
-- statement:
--   For the true stopped original Gaussian uniform grid, the strict event that the deterministic gridpoint precedes the actual stopping time is measurable in the sigma-algebra at its clipped stopped starting clock. This directly allows physical Gaussian derivative and Hessian coefficients to use the strict active-cell indicator while remaining measurable at the actual starting stopping time, so no post-stopping Brownian increment enters the true centred source.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_clipped_gaussian_active_cell_stopped_history
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a24_original_clipped_gaussian_active_mask_stoppingSigma
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (σ τ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (s : ℝ≥0) (hτ : ∀ ω, τ ω = min s (σ ω))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    MeasurableSet[hτstop.measurableSpace] {ω : Ω | s < σ ω}:= by sorry
