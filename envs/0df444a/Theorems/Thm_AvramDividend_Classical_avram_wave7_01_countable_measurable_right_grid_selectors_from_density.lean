-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_measurable_right_grid_selectors_from_density
-- name    : AvramDividend.Classical.avram_wave7_01_countable_measurable_right_grid_selectors_from_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:03:29.214043+00:00
-- url     : https://prove2.me/theorems/3b476d96-c4cb-40e1-b37f-c220757d9a49
-- title:
--   Countably many measurable right-grid approximations to arbitrary path-dependent times
-- statement:
--   For a dense countable nonnegative-time grid, any product-measurable random coordinate-path time and any sequence of positive widths, choose a jointly indexed family of measurable natural-valued grid indices with a point in each short strict right interval. This discharges the abstract interval-existence premise of the accepted right selector uniformly over all approximation scales.
-- source:
--   Use DenseRange.exists_between on t(Y)<t(Y)+ε_n, apply the Proved right-grid measurable selector for each n, then assemble the countable choice of indices and their measurability by Classical.choose.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_right_grid_selector_for_jump_marks

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_countable_measurable_right_grid_selectors_from_density
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (t : (ℝ≥0 → ℝ) → ℝ≥0) (ht : Measurable t)
    (ε : ℕ → ℝ≥0) (hε : ∀ n, 0 < ε n) :
    ∃ index : ℕ → (ℝ≥0 → ℝ) → ℕ,
      (∀ n : ℕ, Measurable (index n)) ∧
      ∀ (n : ℕ) (Y : ℝ≥0 → ℝ),
        t Y < grid (index n Y) ∧
        grid (index n Y) < t Y + ε n := by sorry
