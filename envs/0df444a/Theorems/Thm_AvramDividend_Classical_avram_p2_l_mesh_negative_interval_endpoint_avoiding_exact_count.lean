-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_negative_interval_endpoint_avoiding_exact_count
-- name    : AvramDividend.Classical.avram_p2_l_mesh_negative_interval_endpoint_avoiding_exact_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:38:34.798848+00:00
-- url     : https://prove2.me/theorems/add1925e-63d7-455e-9fa3-41d7cbbead4c
-- title:
--   Negative interval endpoint avoidance yields exact uniform-grid intrinsic jump count
-- statement:
--   For a cadlag path and a negative interval (a,b] separated by rho, if no significant genuine jump mark equals a or b, then sufficiently fine original right-closed uniform meshes have exactly the same number of (a,b]-marked increments as genuine jumps in the interval. The interval endpoint atom exclusion is explicit.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_boundary_counts_eventually_exact

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_negative_interval_endpoint_avoiding_exact_count
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (a b ρ : ℝ) (hρ : 0 < ρ) (hbneg : b ≤ -ρ)
    (hEndpoint : ∀ u : ℝ≥0, 0 < u → u ≤ T →
      ρ ≤ |Y u - Function.leftLim Y u| →
      Y u - Function.leftLim Y u ≠ a ∧
        Y u - Function.leftLim Y u ≠ b)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop,
        ((Finset.range (n + 1)).filter (fun i : ℕ =>
          Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈ Ioc a b)).card =
        (S.filter (fun u => Y u - Function.leftLim Y u ∈ Ioc a b)).card := by sorry
