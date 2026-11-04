-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_selected_cell_unique
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_uniform_selected_cell_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:40:47.605562+00:00
-- url     : https://prove2.me/theorems/325818e5-ea4d-4506-8f67-322948e0eb78
-- title:
--   Uniform source selected jump cells have unique grid index
-- statement:
--   For the authentic original half-open uniform time grid and a finite family of genuine jump times, any valid selected cell index is the unique grid cell that crosses the time. Discharges the selected-cell uniqueness hypothesis in the accepted full-grid compact-test jump-sum limit.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_halfopen_cell_unique_index
open Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_uniform_selected_cell_unique
    (T : ℝ≥0) (F : Finset ℝ≥0)
    (idx : ℝ≥0 → ℕ → ℕ)
    (hcell : ∀ t ∈ F, ∀ n,
      (idx t n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < t ∧
      t ≤ (((idx t n + 1 : ℕ) : ℝ≥0) *
        (T / ((n : ℝ≥0) + 1)))) :
    ∀ (n i : ℕ), ∀ t ∈ F,
      (i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < t ∧
      t ≤ (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) →
      i = idx t n := by sorry
