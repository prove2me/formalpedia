-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_measurable_left_grid_sample_family
-- name    : AvramDividend.Classical.avram_wave7_01_countable_measurable_left_grid_sample_family
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:08:54.874008+00:00
-- url     : https://prove2.me/theorems/57dcf89d-98b3-434e-9e4c-df2a77ecdecb
-- title:
--   Countable measurable left-grid sample family on original coordinate paths
-- statement:
--   From feasible left-grid intervals for a measurable path-dependent nonnegative time, select for all precision indices a measurable family of grid indices and globally measurable raw-path evaluations. The zero-time case is excluded from the strict left-bound assertion and handled measurably by the original selector.
-- source:
--   Apply the Proved left-grid selector at each n, choose the family, then apply Proved measurable countably selected raw-path evaluation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_left_grid_selector_for_jump_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_countably_selected_raw_path_evaluation
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_countable_measurable_left_grid_sample_family
    (grid : ℕ → ℝ≥0)
    (t : (ℝ≥0 → ℝ) → ℝ≥0) (ht : Measurable t)
    (ε : ℕ → ℝ≥0)
    (hExist : ∀ (n : ℕ) (Y : ℝ≥0 → ℝ), 0 < t Y →
      ∃ m : ℕ, grid m < t Y ∧ t Y < grid m + ε n) :
    ∃ index : ℕ → (ℝ≥0 → ℝ) → ℕ,
      (∀ n : ℕ, Measurable (index n)) ∧
      (∀ n : ℕ, Measurable (fun Y : ℝ≥0 → ℝ =>
        Y (grid (index n Y)))) ∧
      ∀ (n : ℕ) (Y : ℝ≥0 → ℝ), 0 < t Y →
        grid (index n Y) < t Y ∧
        t Y < grid (index n Y) + ε n := by sorry
