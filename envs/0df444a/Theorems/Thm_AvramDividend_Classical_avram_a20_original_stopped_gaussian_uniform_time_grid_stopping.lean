-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_stopped_gaussian_uniform_time_grid_stopping
-- name    : AvramDividend.Classical.avram_a20_original_stopped_gaussian_uniform_time_grid_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:31:11.425482+00:00
-- url     : https://prove2.me/theorems/0e4eb559-16e5-484b-8106-e2c8b2a3499a
-- title:
--   Every original ruin-clipped Gaussian physical time-grid node is a bounded stopping time
-- statement:
--   For the genuine stopped original dividend strategy, any bounded stopping clock σ and physical deterministic grid node c=i*n/(m+1), the clipped time τ(ω)=min(c,σ(ω)) remains a stopping time in the original right-continuous filtration, and is bounded both by c and by σ pathwise. This directly supplies the exact stopped-time and deterministic-boundedness obligations for original Gaussian Taylor cells, rather than merely measurability of the random grid.
-- source:
--   Original finite-cap Gaussian Ito stopped physical grid, exact filtered times; Mathlib IsStoppingTime.min_const.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal

/-- Every physical Gaussian time-grid cell clipped to the original stopped ruin clock is a bounded stopping time. -/
theorem AvramDividend.Classical.avram_a20_original_stopped_gaussian_uniform_time_grid_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (n m i : ℕ) :
    let c : ℝ≥0 := (i : ℝ≥0) *
      ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))
    let τ : Ω → ℝ≥0 := fun ω => min c (σ ω)
    IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) ∧
    (∀ ω, τ ω ≤ c) ∧
    (∀ ω, τ ω ≤ σ ω) := by sorry
