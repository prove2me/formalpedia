-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_boundary_counts_eventually_exact
-- name    : AvramDividend.Classical.avram_p2_l_mesh_boundary_counts_eventually_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:16:00.168085+00:00
-- url     : https://prove2.me/theorems/05c14fcf-b925-4453-bb8e-548d7852e756
-- title:
--   Fine uniform meshes eventually count negative boundary-avoiding jumps exactly
-- statement:
--   For a genuine cadlag path and a separated negative mark set B, if every significant intrinsic jump mark lies in the interior of B or its complement, then the original right-closed uniform mesh eventually has exactly as many B-marked cells as the path has intrinsic B-marked jump times. This follows from the verified real indicator-sum convergence and integer count stabilisation, and preserves time-zero exclusion and the horizon endpoint.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_boundary_avoiding_indicator_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_nat_count_stabilises_of_real_limit

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators
open scoped Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_boundary_counts_eventually_exact
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (B : Set ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hBsep : B ⊆ Iic (-ρ))
    (hlocal : ∀ u : ℝ≥0, 0 < u → u ≤ T →
      ρ ≤ |Y u - Function.leftLim Y u| →
      Y u - Function.leftLim Y u ∈ interior B ∨
        Y u - Function.leftLim Y u ∈ interior (Bᶜ))
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop,
        ((Finset.range (n + 1)).filter (fun i : ℕ =>
          Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈ B)).card =
        (S.filter (fun u => Y u - Function.leftLim Y u ∈ B)).card := by sorry
