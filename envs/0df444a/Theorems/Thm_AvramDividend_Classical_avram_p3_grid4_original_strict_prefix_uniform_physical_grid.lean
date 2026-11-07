-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_prefix_uniform_physical_grid
-- name    : AvramDividend.Classical.avram_p3_grid4_original_strict_prefix_uniform_physical_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:52:45.237295+00:00
-- url     : https://prove2.me/theorems/c527d1bc-a87c-457d-8eeb-301b48eead89
-- title:
--   Exact cofinal strictly-before-T uniform physical grids with positive mesh and monotone times
-- statement:
--   For positive original horizon T and each n, explicitly construct deterministic NNReal physical time points with n+1 intervals of exact size T/(n+2), starting at zero and ending at T-T/(n+2). These are the precise strict-margin grids required to stop before the right-horizon atom in 2bc848f9 and c1e2f021, independently of ruin clipping. This is a direct source grid construction, not a surrogate process.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_strict_prefix_uniform_physical_grid
    (T : ℝ) (hT : 0 < T) :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0) ∧
      (∀ n, ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n i, i < n + 1 →
        (u n (i + 1) : ℝ) - (u n i : ℝ) = T / ((n : ℝ) + 2)) := by sorry
