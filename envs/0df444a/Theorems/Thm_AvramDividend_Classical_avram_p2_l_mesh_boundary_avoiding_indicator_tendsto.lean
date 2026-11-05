-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_boundary_avoiding_indicator_tendsto
-- name    : AvramDividend.Classical.avram_p2_l_mesh_boundary_avoiding_indicator_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:52:13.512176+00:00
-- url     : https://prove2.me/theorems/526640ca-09da-4375-80d4-52f358565b50
-- title:
--   Original finite-grid negative indicator counts converge when all actual jump marks avoid the band boundary
-- statement:
--   For an arbitrary separated negative mark set B and a genuine cadlag path, show convergence of the full uniform-grid B-indicator sums to the finite intrinsic jump count, under the exact condition that all significant actual jump marks are locally on one side of B's topological boundary. Explicitly excludes false unconditional convergence for arbitrary Borel indicators with boundary atoms. Source is deterministic with no rates or compensators.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_full_grid_local_mark_continuity
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_indicator_continuous_at_interior_side

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_l_mesh_boundary_avoiding_indicator_tendsto
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (B : Set ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hBsep : B ⊆ Set.Iic (-ρ))
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
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          B.indicator (fun _ : ℝ => (1 : ℝ))
            (Y (((i + 1 : ℕ) : ℝ≥0) *
              (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (∑ u ∈ S,
          B.indicator (fun _ : ℝ => (1 : ℝ))
            (Y u - Function.leftLim Y u))) := by sorry
