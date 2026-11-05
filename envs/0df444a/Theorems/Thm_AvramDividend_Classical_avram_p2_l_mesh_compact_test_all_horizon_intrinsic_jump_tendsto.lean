-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_all_horizon_intrinsic_jump_tendsto
-- name    : AvramDividend.Classical.avram_p2_l_mesh_compact_test_all_horizon_intrinsic_jump_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:02:10.025996+00:00
-- url     : https://prove2.me/theorems/7c0f7ab8-4b95-43c5-87cf-d46448a7241b
-- title:
--   Original grid to intrinsic cadlag compact-test convergence including the zero horizon
-- statement:
--   Remove the positive-horizon premise from the original-source finite uniform-grid compact negative-test convergence theorem. At positive horizons, apply the verified original-grid convergence theorem. At T=0, show the selected intrinsic jump-time set is empty because there is no strictly positive time at or before zero, every original grid increment is Y(0)-Y(0)=0, and the test vanishes at zero since its support is strictly negative. No fake jump is introduced at the origin, and jumps at a positive terminal horizon remain included.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_uniform_grid_intrinsic_jump_tendsto

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_compact_test_all_horizon_intrinsic_jump_tendsto (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (hL : ∀ t : ℝ≥0, Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t))) (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) (f : ℝ → ℝ) (hfcomp : HasCompactSupport f) (hfcont : Continuous f) (hf : ∀ z : ℝ, -ρ < z → f z = 0) : ∃ S : Finset ℝ≥0, (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ ρ ≤ |Y u - Function.leftLim Y u|) ∧ Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), f (Y (((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) - Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) atTop (𝓝 (∑ u ∈ S, f (Y u - Function.leftLim Y u))) := by sorry
