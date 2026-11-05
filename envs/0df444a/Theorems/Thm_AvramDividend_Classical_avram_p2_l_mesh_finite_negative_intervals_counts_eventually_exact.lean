-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_negative_intervals_counts_eventually_exact
-- name    : AvramDividend.Classical.avram_p2_l_mesh_finite_negative_intervals_counts_eventually_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:54:14.583362+00:00
-- url     : https://prove2.me/theorems/b6dffa76-0eef-45e1-b4d2-ea1634e2fb88
-- title:
--   Simultaneous exact original-mesh histogram of finite negative intervals
-- statement:
--   For a finite set of negative half-open interval marks with no significant intrinsic jumps exactly on the endpoints, sufficiently fine original uniform grids count each interval's intrinsic jumps exactly on a common mesh.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_negative_interval_endpoint_avoiding_exact_count

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_finite_negative_intervals_counts_eventually_exact {ι : Type*} [Fintype ι]
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
      ∀ᶠ n : ℕ in atTop, ∀ i : ι,
        ((Finset.range (n + 1)).filter (fun j : ℕ =>
          Y (((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈
            Ioc (a i) (b i))).card =
        (S.filter (fun u => Y u - Function.leftLim Y u ∈
          Ioc (a i) (b i))).card := by sorry
