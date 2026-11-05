-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_strict_negative_compact_test_intrinsic_tendsto
-- name    : AvramDividend.Classical.avram_p2_l_mesh_strict_negative_compact_test_intrinsic_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:16:19.249109+00:00
-- url     : https://prove2.me/theorems/1f665611-acaa-4728-b742-0bdecbb74c34
-- title:
--   Compact strictly negative tests: original uniform grid converges to genuine intrinsic jumps without supplied cutoff
-- statement:
--   For a genuine real cadlag path on a positive finite horizon and any continuous compactly supported real test whose topological support lies wholly below zero, construct a positive negative-mark cutoff automatically and prove that the tested original uniform-grid increments converge to the tested intrinsic finite significant jump sum. The proof combines the independently verified support-gap theorem and complete original-grid compact-test convergence; all assumptions and conclusions refer to the same original path and its actual left limits.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_negative_support_has_strict_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_uniform_grid_intrinsic_jump_tendsto

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_strict_negative_compact_test_intrinsic_tendsto (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T) (hL : ∀ t : ℝ≥0, Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t))) (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) (f : ℝ → ℝ) (hfcomp : HasCompactSupport f) (hfcont : Continuous f) (hneg : tsupport f ⊆ Iio (0 : ℝ)) : ∃ ρ : ℝ, 0 < ρ ∧ ∃ S : Finset ℝ≥0, (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ ρ ≤ |Y u - Function.leftLim Y u|) ∧ Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), f (Y (((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) - Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) atTop (𝓝 (∑ u ∈ S, f (Y u - Function.leftLim Y u))) := by sorry
