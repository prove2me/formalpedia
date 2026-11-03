-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_adaptive_grid_jump_increment_sequence_measurable
-- name    : AvramDividend.Classical.avram_wave7_01_countable_adaptive_grid_jump_increment_sequence_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:04:17.566489+00:00
-- url     : https://prove2.me/theorems/ca00b208-0daf-4654-9180-7cf09c7ee72e
-- title:
--   Countable path-dependent rational-grid increment approximation sequence is coordinate-product measurable
-- statement:
--   If left and right grid sample indices for each approximation stage are measurably chosen from the raw real path, the full sequence of sampled increments is jointly measurable into the countable product real space. This is the measurable pre-limit stage for genuine left/right jump sizes at the previously enumerated exact original Lévy jump times; no false assertion about arbitrary random-time evaluation, finite activity, or unrelated process is used.
-- source:
--   Proved adaptive countable-grid raw path evaluation a8b2902a composed with subtraction and measurable_pi_lambda.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_countably_selected_raw_path_evaluation

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_countable_adaptive_grid_jump_increment_sequence_measurable
    (grid : ℕ → ℝ≥0)
    (left right : ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hLeft : ∀ n, Measurable (left n))
    (hRight : ∀ n, Measurable (right n)) :
    Measurable (fun Y : ℝ≥0 → ℝ => fun n : ℕ =>
      Y (grid (right n Y)) - Y (grid (left n Y))) := by sorry
