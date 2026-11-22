-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_clipped_gaussian_active_cell_stopped_history
-- name    : AvramDividend.Classical.avram_a24_original_clipped_gaussian_active_cell_stopped_history
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:07:33.703997+00:00
-- url     : https://prove2.me/theorems/f0243bcf-d608-40ea-a69a-d985ac7de439
-- title:
--   Original clipped uniform Gaussian active-cell event is measurable in the stopped history
-- statement:
--   For the exact original bounded random stopping clock and any deterministic Gaussian uniform mesh time s, if a physical cell starts at the stopped time min(s,sigma), then the event that the cell is active (s<sigma) is measurable in the stopped-time history, as witnessed by its intersection with every stopping-time threshold event. This enables genuinely stopped, predictable active-cell Gaussian gradient and Hessian coefficients to vanish beyond the actual original stopped clock, without looking into the future.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a24_original_clipped_gaussian_active_cell_stopped_history
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (σ τ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (s : ℝ≥0) (hτ : ∀ ω, τ ω = min s (σ ω)) :
    ∀ t : ℝ≥0,
      MeasurableSet[𝓕.rightCont t]
        ({ω : Ω | s < σ ω} ∩ {ω : Ω | τ ω ≤ t}):= by sorry
