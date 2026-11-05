-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_eventually_nonzero_test_grid_count_le_large_jumps
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_eventually_nonzero_test_grid_count_le_large_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:29:06.011288+00:00
-- url     : https://prove2.me/theorems/107afdc5-bc33-4f3c-9991-e1050fc94735
-- title:
--   Eventually at most one nonzero test grid cell per selected actual jump
-- statement:
--   For a real càdlàg path on a positive finite horizon and a test vanishing around zero, every sufficiently fine grid has no more nonzero test increments than the finite selected set of actual jumps above the support radius. The right-closed cell convention covers a jump exactly at a grid endpoint. Assumes only the established càdlàg sided limits and finite locator conditions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_uniform_test_zero_outside_all_large_jump_cells
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_finite_nonzero_grid_cells_count_le_selected_jumps

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_h_cadlag_eventually_nonzero_test_grid_count_le_large_jumps
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ) (f : ℝ → ℝ)
    (hfzero : ∀ z : ℝ, |z| < ρ → f z = 0)
    (S : Finset ℝ≥0)
    (hS : ∀ t : ℝ≥0, 0 < t → t ≤ T →
      ρ ≤ |Y t - Function.leftLim Y t| → t ∈ S)
    (j : ℝ≥0 → ℕ → ℕ)
    (hj : ∀ u ∈ S, ∀ n : ℕ,
      j u n ≤ n ∧
      (j u n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
      u ≤ (((j u n + 1 : ℕ) : ℝ≥0) *
        (T / ((n : ℝ≥0) + 1))))
    (hL : ∀ t, t ≤ T →
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t, t ≤ T → ContinuousWithinAt Y (Ici t) t) :
    ∀ᶠ n : ℕ in atTop,
      ((Finset.range (n + 1)).filter (fun i =>
        f (Y (((i + 1 : ℕ) : ℝ≥0) *
          (T / ((n : ℝ≥0) + 1))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))) ≠ 0)).card ≤ S.card := by sorry
