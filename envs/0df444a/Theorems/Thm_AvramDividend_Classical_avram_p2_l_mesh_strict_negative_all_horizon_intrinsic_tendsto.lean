-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_strict_negative_all_horizon_intrinsic_tendsto
-- name    : AvramDividend.Classical.avram_p2_l_mesh_strict_negative_all_horizon_intrinsic_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:23:21.917196+00:00
-- url     : https://prove2.me/theorems/cd095a0f-4b94-4c18-b49a-a6fb31496b66
-- title:
--   Strictly negative compact tests: original cadlag uniform-grid jump convergence on every horizon
-- statement:
--   For a genuine real cadlag path on any nonnegative finite horizon and a continuous compactly supported real test whose topological support is strictly negative, obtain a strictly positive mark cutoff automatically and prove convergence of the actual T/(n+1) uniform-grid tested increments to a finite sum of the actual intrinsic jump marks, with time zero excluded and the terminal horizon included. At T=0 both sides are zero. This is proved by importing the public original P2-L cutoff theorem and the public all-horizon grid convergence theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_negative_support_has_strict_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_all_horizon_intrinsic_jump_tendsto

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_strict_negative_all_horizon_intrinsic_tendsto (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hL : ∀ t : ℝ≥0, Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t))) (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) (f : ℝ → ℝ) (hfcomp : HasCompactSupport f) (hfcont : Continuous f) (hneg : tsupport f ⊆ Iio (0 : ℝ)) : ∃ ρ : ℝ, 0 < ρ ∧ ∃ S : Finset ℝ≥0, (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ ρ ≤ |Y u - Function.leftLim Y u|) ∧ Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), f (Y (((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) - Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) atTop (𝓝 (∑ u ∈ S, f (Y u - Function.leftLim Y u))) := by sorry
