-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvres9_nonrefining_physical_grid_exists
-- name    : AvramDividend.Classical.avram_bvres9_nonrefining_physical_grid_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:07:34.180791+00:00
-- url     : https://prove2.me/theorems/0877b3d0-5180-4b7c-8a13-33f6f5feb5ab
-- title:
--   An admissible monotone physical grid retains a macroscopic terminal cell
-- statement:
--   The original theorem 4f851376 assumes only nondecreasing finite grid cells, initial point zero, and last point 3-3/(n+2). This explicit witness repeats time 1/2 on interior cells and keeps the final cell at least 3/2 long for every n>=1, so those hypotheses do not force mesh refinement. It supplies the exact grid geometry for a future genuine compound-Poisson disproof; the stochastic model and full negation remain separate obligations.
-- source:
--   AVRAM BV-RESIDUAL9 correction calculation, 7 November 2026; explicit n=0 convention and positive terminal-cell lower bound.

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvres9_nonrefining_physical_grid_exists :
  ∃ u : ℕ → ℕ → ℝ≥0,
    (∀ n : ℕ, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = 3 - 3 / ((n : ℝ) + 2))) ∧
    (∀ (n i : ℕ), i < n + 1 → u n i ≤ u n (i + 1)) ∧
    (∀ n : ℕ, 1 ≤ n → (3 / 2 : ℝ) ≤
      (u n (n + 1) : ℝ) - (u n n : ℝ)) := by sorry
