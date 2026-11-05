-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_uniform_grid_intrinsic_test_difference_envelope
-- name    : AvramDividend.Classical.avram_p2_l_mesh_uniform_grid_intrinsic_test_difference_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:48:22.131678+00:00
-- url     : https://prove2.me/theorems/f0a51831-a34e-49e4-aa21-0760f840ada7
-- title:
--   Uniform bound for original grid and intrinsic finite jump test-sum discrepancy
-- statement:
--   For a genuine cadlag path, every bounded test supported below a fixed negative threshold has its original uniform-mesh sum and finite intrinsic jump sum simultaneously bounded in difference by twice the large-jump count times the test bound, on all sufficiently fine meshes.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_uniform_all_negative_test_sum_envelope

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_uniform_grid_intrinsic_test_difference_envelope
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ,
        (∀ z : ℝ, -ρ < z → f z = 0) →
        ∀ M : ℝ, 0 ≤ M → (∀ z : ℝ, |f z| ≤ M) →
        |(∑ i ∈ Finset.range (n + 1),
          f (Y (((i + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) -
          (∑ u ∈ S, f (Y u - Function.leftLim Y u))| ≤
          2 * (S.card : ℝ) * M := by sorry
