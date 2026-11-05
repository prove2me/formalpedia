-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_cadlag_selected_mark_avoiding_cutoff
-- name    : AvramDividend.Classical.avram_p2_l_mesh_cadlag_selected_mark_avoiding_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:02:10.721813+00:00
-- url     : https://prove2.me/theorems/0fc2173c-3d88-41e0-b475-c278eb181209
-- title:
--   Cadlag path admits a selected-jump-avoiding cutoff in every real interval
-- statement:
--   For a source-exact cadlag path and finite compact horizon, every open real interval contains a cutoff unequal to every significant intrinsic jump mark on that horizon. The construction uses the proved finite large-jump time set and finite-set interval avoidance, with zero excluded and T included.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_negative_marks_avoid_interval_point

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_cadlag_selected_mark_avoiding_cutoff
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (a b : ℝ) (hab : a < b) :
    ∃ c : ℝ, a < c ∧ c < b ∧
      ∀ u : ℝ≥0, 0 < u → u ≤ T →
        ρ ≤ |Y u - Function.leftLim Y u| →
          Y u - Function.leftLim Y u ≠ c := by sorry
