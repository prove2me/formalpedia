-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_original_grid_adjacent_duration
-- name    : AvramDividend.Classical.avram_p2_34dbea70_uniform_original_grid_adjacent_duration
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:46:37.98028+00:00
-- url     : https://prove2.me/theorems/3016067b-4113-4667-a441-e557273cc83f
-- title:
--   Each adjacent uniform NNReal grid cell has exactly its stated width
-- statement:
--   For any time horizon T, grid resolution n and cell index i, the difference of adjacent uniform nonnegative real grid times is exactly T/(n+1). The conclusion uses the same NNReal truncated subtraction appearing in the Proved original Lévy stationary-grid mean formula, bridging it to the Proved original-process rare-increment probability bound.

import Mathlib

open scoped NNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_uniform_original_grid_adjacent_duration
    (T : ℝ≥0) (n i : ℕ) :
    (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
      (i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) =
    T / ((n : ℝ≥0) + 1) := by sorry
