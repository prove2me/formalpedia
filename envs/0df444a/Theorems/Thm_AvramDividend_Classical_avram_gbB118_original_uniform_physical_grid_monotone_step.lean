-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB118_original_uniform_physical_grid_monotone_step
-- name    : AvramDividend.Classical.avram_gbB118_original_uniform_physical_grid_monotone_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:26:03.943092+00:00
-- url     : https://prove2.me/theorems/08efafe4-0f03-4420-abeb-80ffc6b6c65d
-- title:
--   Original uniform physical grid has monotone times, zero start and exact constant cell width
-- statement:
--   For every horizon n and mesh parameter m, the original physical grid s_i=i*n/(m+1) in nonnegative-real time is monotone, starts at zero, and satisfies s_(i+1)=s_i+n/(m+1). This discharges exact time-grid hypotheses required by the Gaussian stopped-prefix noise and L1 source certificates without changing the original mesh.

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB118_original_uniform_physical_grid_monotone_step
    (n m : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    Monotone s ∧ s 0 = 0 ∧
      ∀ i : ℕ, s (i + 1) = s i + Δ := by sorry
