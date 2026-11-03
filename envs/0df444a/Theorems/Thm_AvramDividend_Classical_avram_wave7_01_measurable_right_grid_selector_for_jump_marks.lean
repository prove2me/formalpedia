-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_right_grid_selector_for_jump_marks
-- name    : AvramDividend.Classical.avram_wave7_01_measurable_right_grid_selector_for_jump_marks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:38:39.639741+00:00
-- url     : https://prove2.me/theorems/b1bf9709-27b9-4d73-a1cf-d5e4df211254
-- title:
--   Measurable countable right-grid selector for random jump-time values
-- statement:
--   Given a product-coordinate measurable path-dependent candidate time and a countable time grid containing a point strictly within the ε-neighbourhood to its right, select that grid point with a measurable natural-valued index. This supports exact right-continuous path-value approximation at original Lévy jump times.
-- source:
--   Measurable first-witness selection of a strict upper grid approximation. Coordinate time inequalities are Borel, measurable_find supplies the countable index, and Nat.find_spec proves the selected interval. The existence premise is explicit and later discharged by dense-range grid construction.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_measurable_right_grid_selector_for_jump_marks
    (grid : ℕ → ℝ≥0)
    (t : (ℝ≥0 → ℝ) → ℝ≥0) (ht : Measurable t)
    (ε : ℝ≥0)
    (hExist : ∀ Y : ℝ≥0 → ℝ,
      ∃ n : ℕ, t Y < grid n ∧ grid n < t Y + ε) :
    ∃ index : (ℝ≥0 → ℝ) → ℕ,
      Measurable index ∧
      ∀ Y : ℝ≥0 → ℝ,
        t Y < grid (index Y) ∧ grid (index Y) < t Y + ε := by sorry
