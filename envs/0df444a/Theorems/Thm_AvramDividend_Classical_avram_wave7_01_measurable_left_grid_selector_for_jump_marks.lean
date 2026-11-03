-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_left_grid_selector_for_jump_marks
-- name    : AvramDividend.Classical.avram_wave7_01_measurable_left_grid_selector_for_jump_marks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:35:33.029199+00:00
-- url     : https://prove2.me/theorems/9889a2e3-ff4c-4607-9136-866e78dd269d
-- title:
--   Measurable countable left-grid selector for randomly chosen jump times
-- statement:
--   Given a coordinate-product measurable candidate jump time and a countable time grid with an available point in the short interval immediately to its left, select such a grid point with a measurable natural-valued index. This supplies the exact discrete-selection step needed before measurable one-sided path-value approximation at intrinsic jump times. Existence is made an explicit hypothesis and must later be proved from grid density.
-- source:
--   Countable-first-hit measurable selection: classify each path by the least grid index satisfying strict interval inequalities, using Mathlib Nat.find and measurability of singleton fibres; positive-time fallback branch. Intended to compose with original path first-downcrossing times and Proved selected-grid evaluation.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_measurable_left_grid_selector_for_jump_marks
    (grid : ℕ → ℝ≥0)
    (t : (ℝ≥0 → ℝ) → ℝ≥0) (ht : Measurable t)
    (ε : ℝ≥0)
    (hExist : ∀ Y : ℝ≥0 → ℝ, 0 < t Y →
      ∃ n : ℕ, grid n < t Y ∧ t Y < grid n + ε) :
    ∃ index : (ℝ≥0 → ℝ) → ℕ,
      Measurable index ∧
      ∀ Y : ℝ≥0 → ℝ, 0 < t Y →
        grid (index Y) < t Y ∧ t Y < grid (index Y) + ε := by sorry
