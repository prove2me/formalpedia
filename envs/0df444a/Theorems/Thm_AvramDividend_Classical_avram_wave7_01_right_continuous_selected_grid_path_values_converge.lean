-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_right_continuous_selected_grid_path_values_converge
-- name    : AvramDividend.Classical.avram_wave7_01_right_continuous_selected_grid_path_values_converge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:49:48.303576+00:00
-- url     : https://prove2.me/theorems/dccc9b0a-4838-441e-81f7-c3dc6a1c9d1a
-- title:
--   Right-continuous càdlàg paths recover exact values from shrinking selected grid times
-- statement:
--   If selected countable-grid times are trapped between t(Y) and t(Y)+ε_n with ε_n→0, then for any coordinate path right-continuous at t(Y) those sampled path values converge to Y(t(Y)). The theorem handles a genuinely random/path-dependent time and yields the pathwise correctness needed to combine measurable right-grid selectors with a globally measurable real limit envelope.
-- source:
--   Squeeze selected grid times between constant t(Y) and t(Y)+ε_n, upgrade convergence to the relative right-neighbourhood using their order bound, and compose with the supplied ContinuousWithinAt condition.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_right_continuous_selected_grid_path_values_converge
    (grid : ℕ → ℝ≥0) (t : (ℝ≥0 → ℝ) → ℝ≥0)
    (ε : ℕ → ℝ≥0) (hε : Tendsto ε atTop (𝓝 0))
    (index : ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hBounds : ∀ (Y : ℝ≥0 → ℝ) (n : ℕ),
      t Y ≤ grid (index n Y) ∧
      grid (index n Y) ≤ t Y + ε n) :
    ∀ Y : ℝ≥0 → ℝ,
      ContinuousWithinAt Y (Ici (t Y)) (t Y) →
      Tendsto (fun n : ℕ => Y (grid (index n Y)))
        atTop (𝓝 (Y (t Y))) := by sorry
