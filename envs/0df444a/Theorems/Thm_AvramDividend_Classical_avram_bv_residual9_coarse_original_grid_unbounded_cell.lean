-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_coarse_original_grid_unbounded_cell
-- name    : AvramDividend.Classical.avram_bv_residual9_coarse_original_grid_unbounded_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:38:58.36899+00:00
-- url     : https://prove2.me/theorems/cde7fe56-1ff8-467c-8f35-00391cde5511
-- title:
--   Original stopped-grid endpoint and monotonicity axioms permit a fixed-size unrefined final physical cell
-- statement:
--   There exists a concrete physical grid satisfying exactly the original theorem's zero-start, prescribed penultimate horizon, and monotonicity assumptions, for which the last cell has length at least three halves for every index. Hence those assumptions alone do not force a refining mesh, and the original vanishing-error argument requires attention to this gap.
-- source:
--   Source-exact algebraic obstacle for Avram 4f851376: T=3; all interior grid marks equal zero; final mark equals 3 - 3/(n+2).

import Mathlib
open scoped NNReal

theorem AvramDividend.Classical.avram_bv_residual9_coarse_original_grid_unbounded_cell :
    ∃ u : ℕ → ℕ → NNReal,
      (∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = 3 - 3 / ((n : ℝ) + 2))) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n, (3 / 2 : ℝ) ≤ (u n (n + 1) : ℝ) - (u n n : ℝ)) := by sorry
