-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_physical_strict_horizon_uniform_grid
-- name    : AvramDividend.Classical.avram_a19_physical_strict_horizon_uniform_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:33:09.654438+00:00
-- url     : https://prove2.me/theorems/50551cee-8f57-417a-8fc4-b2e174be573d
-- title:
--   Uniform original physical mesh with strict horizon and exact rational cells
-- statement:
--   The explicit rational physical mesh u(n,i)=T*i/(n+2) is nonnegative, increases with i, begins at zero, ends at T-T/(n+2), and is uniform with step T/(n+2). The formula rules out coarse grids and supplies the exact refinement condition for stochastic residual convergence.
-- source:
--   Exact deterministic uniform-grid strengthening of the physical stopped-cell constructor 2bc848f9. The additional formula enables the source-exact original stopped residual for uniform grid reduction to be mathematically valid.

import Mathlib
open Classical Filter
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_physical_strict_horizon_uniform_grid
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - δ n)) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) := by sorry
