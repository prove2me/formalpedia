-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_finite_actual_jump_cell_test_sum_tendsto
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_finite_actual_jump_cell_test_sum_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:12:16.8012+00:00
-- url     : https://prove2.me/theorems/20eb0318-1adf-42a9-a72e-33c64ef93842
-- title:
--   Finite genuine jump-test sums converge along their exact half-open uniform cells
-- statement:
--   For an arbitrary real càdlàg path supplied through genuine left and right limits on finitely many actual jump times, explicitly choose uniform right-closed cells at each mesh resolution. The corresponding full finite sum of continuous test values of actual path increments converges to the finite sum of actual intrinsic jump-test values. Handles mesh endpoint equality and the terminal time T. This is the true finite significant-cell contribution to mesh-to-jump convergence; exclusion of spurious other grid cells remains separate.

import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_source_jump_cells_sided_limits
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_shrinking_cell_increment_converges_to_actual_jump

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_h_cadlag_finite_actual_jump_cell_test_sum_tendsto
    (Y : ℝ≥0 → ℝ) (S : Finset ℝ≥0)
    (T : ℝ≥0) (hT : 0 < T)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hTimes : ∀ u ∈ S, 0 < u ∧ u ≤ T)
    (hL : ∀ u ∈ S,
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hR : ∀ u ∈ S, ContinuousWithinAt Y (Ici u) u) :
    ∃ idx : ℝ≥0 → ℕ → ℕ,
      (∀ u ∈ S, ∀ n, idx u n ≤ n ∧
        (idx u n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧ u ≤ ((idx u n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∧
      Tendsto (fun n : ℕ =>
        ∑ u ∈ S, f (Y (((idx u n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) - Y ((idx u n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (∑ u ∈ S, f (Y u - Function.leftLim Y u))) := by sorry
