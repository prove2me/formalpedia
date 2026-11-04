-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_halfopen_cell_unique_index
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_uniform_halfopen_cell_unique_index
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:52:39.746484+00:00
-- url     : https://prove2.me/theorems/4d84e8a1-d4b2-44c5-9a89-9b5aff9480f5
-- title:
--   An original jump time belongs to at most one half-open uniform grid cell
-- statement:
--   Two half-open consecutive uniform nonnegative mesh cells cannot both contain the same point, including times exactly aligned with a grid boundary. Proof uses only nonnegative multiplication monotonicity and natural-number successor inequalities; it resolves the unique selected original jump-cell identification needed for the full-grid compact-test limit.

import Mathlib
open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_uniform_halfopen_cell_unique_index
    (u δ : ℝ≥0) (i j : ℕ)
    (hi : (i : ℝ≥0) * δ < u ∧
      u ≤ ((i + 1 : ℕ) : ℝ≥0) * δ)
    (hj : (j : ℝ≥0) * δ < u ∧
      u ≤ ((j + 1 : ℕ) : ℝ≥0) * δ) :
    i = j  := by sorry
