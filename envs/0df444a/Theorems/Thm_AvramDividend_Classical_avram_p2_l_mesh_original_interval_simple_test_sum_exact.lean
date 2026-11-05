-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_original_interval_simple_test_sum_exact
-- name    : AvramDividend.Classical.avram_p2_l_mesh_original_interval_simple_test_sum_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:09:52.290902+00:00
-- url     : https://prove2.me/theorems/5e77c368-9b7b-44b4-8bc3-235c1e0d2755
-- title:
--   Original uniform-grid finite simple negative-interval tests equal intrinsic-jump sums
-- statement:
--   For finite families of negative half-open mark intervals with no actual intrinsic marks on their endpoints, every finite real-weighted interval-indicator test of the complete original T/(n+1) mesh equals the corresponding true intrinsic-jump sum eventually, uniformly in coefficients.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_negative_intervals_counts_eventually_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_weighted_indicator_finset_sum

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_original_interval_simple_test_sum_exact {ι : Type*} [Fintype ι]
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (a b : ι → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hbneg : ∀ i, b i ≤ -ρ)
    (hEndpoint : ∀ (i : ι) (u : ℝ≥0), 0 < u → u ≤ T →
      ρ ≤ |Y u - Function.leftLim Y u| →
      Y u - Function.leftLim Y u ≠ a i ∧
        Y u - Function.leftLim Y u ≠ b i)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop, ∀ c : ι → ℝ,
        (∑ j ∈ Finset.range (n + 1), ∑ i : ι,
          if Y (((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
              Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈
                Ioc (a i) (b i) then c i else 0) =
        (∑ u ∈ S, ∑ i : ι,
          if Y u - Function.leftLim Y u ∈ Ioc (a i) (b i)
          then c i else 0) := by sorry
