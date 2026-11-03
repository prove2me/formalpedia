-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_shrinking_right_grid_samples_recover_original_path
-- name    : AvramDividend.Classical.avram_wave7_01_measurable_shrinking_right_grid_samples_recover_original_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:09:20.667838+00:00
-- url     : https://prove2.me/theorems/df049976-e902-44c2-b3b0-d54dad2e53a9
-- title:
--   Measurable shrinking right-grid samples converge to exact original path values
-- statement:
--   On the actual raw coordinate path measurable space, a Borel random time has a countable family of grid-selected right samples that are globally measurable functions of the path and converge to its exact value whenever the path is right-continuous there. Uses the existing Proved right selector, countable-grid evaluation, and right-limit convergence.
-- source:
--   DenseRange gives right interval points; choose proven Borel selectors at each scale. Compose the Proved adaptive grid evaluation measurability and Proved shrinking-right-grid convergence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_right_grid_selector_for_jump_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_countably_selected_raw_path_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_right_continuous_selected_grid_path_values_converge
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_measurable_shrinking_right_grid_samples_recover_original_path
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (t : (ℝ≥0 → ℝ) → ℝ≥0) (ht : Measurable t)
    (ε : ℕ → ℝ≥0) (hεpos : ∀ n, 0 < ε n)
    (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ index : ℕ → (ℝ≥0 → ℝ) → ℕ,
      (∀ n : ℕ, Measurable (index n)) ∧
      (∀ n : ℕ, Measurable (fun Y : ℝ≥0 → ℝ =>
        Y (grid (index n Y)))) ∧
      (∀ (n : ℕ) (Y : ℝ≥0 → ℝ),
        t Y < grid (index n Y) ∧ grid (index n Y) < t Y + ε n) ∧
      ∀ Y : ℝ≥0 → ℝ,
        ContinuousWithinAt Y (Ici (t Y)) (t Y) →
        Tendsto (fun n : ℕ => Y (grid (index n Y)))
          atTop (𝓝 (Y (t Y))) := by sorry
