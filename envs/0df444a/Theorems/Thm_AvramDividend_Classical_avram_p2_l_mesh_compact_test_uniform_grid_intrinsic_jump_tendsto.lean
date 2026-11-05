-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_uniform_grid_intrinsic_jump_tendsto
-- name    : AvramDividend.Classical.avram_p2_l_mesh_compact_test_uniform_grid_intrinsic_jump_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:54:51.52534+00:00
-- url     : https://prove2.me/theorems/9a40d6a0-79eb-4803-a512-2b8605879265
-- title:
--   Original uniform-grid cadlag compact-marked-test sums converge to genuine intrinsic jumps
-- statement:
--   For an actual real cadlag path on a positive finite NNReal horizon, and a continuous compactly supported real test vanishing strictly to the right of a negative support cutoff, the sums of the tested increments over the original uniform grid converge to the sum over the actual finite set of significant intrinsic jumps. Time zero is excluded, the final uniform cell includes the terminal horizon, left limits use Function.leftLim, and no atom-free boundary or stochastic surrogate is assumed. The approximation premise of the earlier conditional bridge is explicitly constructed using the finite original significant jump marks.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_mark_free_step_density
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_convergence_of_step_approximations

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_compact_test_uniform_grid_intrinsic_jump_tendsto (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T) (ρ : ℝ) (hρ : 0 < ρ) (hL : ∀ t : ℝ≥0, Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t))) (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) (f : ℝ → ℝ) (hfcomp : HasCompactSupport f) (hfcont : Continuous f) (hf : ∀ z : ℝ, -ρ < z → f z = 0) : ∃ S : Finset ℝ≥0, (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ ρ ≤ |Y u - Function.leftLim Y u|) ∧ Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), f (Y (((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) - Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) atTop (𝓝 (∑ u ∈ S, f (Y u - Function.leftLim Y u))) := by sorry
