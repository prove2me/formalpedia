-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_uniform_negative_test_difference_stability
-- name    : AvramDividend.Classical.avram_p2_l_mesh_uniform_negative_test_difference_stability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:49:41.750346+00:00
-- url     : https://prove2.me/theorems/31761a9f-2793-4ba5-8569-b8b7fd0674cb
-- title:
--   Uniform fine-mesh stability under bounded negative-test approximation
-- statement:
--   Two negative-mark test functions that coincide above a strictly negative cutoff and differ uniformly by at most δ have original grid-test sums differing by at most δ times the finite number of significant intrinsic jumps, on every sufficiently fine original uniform mesh. Does not assume desired convergence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_uniform_all_negative_test_sum_envelope

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_uniform_negative_test_difference_stability
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop, ∀ f g : ℝ → ℝ,
        (∀ z : ℝ, -ρ < z → f z = g z) →
        ∀ δ : ℝ, 0 ≤ δ → (∀ z : ℝ, |f z - g z| ≤ δ) →
        |(∑ i ∈ Finset.range (n + 1),
          f (Y (((i + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) -
          (∑ i ∈ Finset.range (n + 1),
          g (Y (((i + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))| ≤
          (S.card : ℝ) * δ := by sorry
