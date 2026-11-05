-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_uniform_all_negative_mark_count_envelope
-- name    : AvramDividend.Classical.avram_p2_l_mesh_uniform_all_negative_mark_count_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:34:35.258424+00:00
-- url     : https://prove2.me/theorems/4be20248-cf12-4e77-8a49-876a2cc552e9
-- title:
--   Uniform finite marked-cell envelope for every separated negative Borel set
-- statement:
--   For a true cadlag path and positive horizon there is one finite set of significant intrinsic jumps and one eventual uniform mesh threshold, so that every measurable or arbitrary negative mark set separated by rho has at most that many grid cells, simultaneously and without assuming mark-boundary avoidance.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_eventually_nonzero_test_grid_count_le_large_jumps
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_jump_test_local_continuity

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_uniform_all_negative_mark_count_envelope
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop, ∀ B : Set ℝ,
        B ⊆ Iic (-ρ) →
        ((Finset.range (n + 1)).filter (fun i : ℕ =>
          Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈ B)).card ≤
        S.card := by sorry
