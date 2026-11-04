-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_original_grid_width_sum
-- name    : AvramDividend.Classical.avram_p2_34dbea70_uniform_original_grid_width_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:05:01.840649+00:00
-- url     : https://prove2.me/theorems/0af48549-4a77-4c99-8437-708b5774b699
-- title:
--   Uniform nonnegative real time mesh widths sum to the whole horizon
-- statement:
--   For any nonnegative time horizon T and n+1 uniform source-grid cells, the exact sum of NNReal mesh widths T/(n+1) equals T. This finite identity will convert the verified original-process per-cell negative-tail bound into an n-independent expected-count bound, without Lévy-rate or compensator assumptions.

import Mathlib

open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_uniform_original_grid_width_sum
    (T : ℝ≥0) (n : ℕ) :
    (∑ _i ∈ Finset.range (n + 1), T / ((n : ℝ≥0) + 1)) = T := by sorry
