-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_indicator_continuous_at_interior_side
-- name    : AvramDividend.Classical.avram_p2_l_mesh_indicator_continuous_at_interior_side
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:23:35.950829+00:00
-- url     : https://prove2.me/theorems/c6a87b14-ba40-4dd5-9209-9887d285d6af
-- title:
--   Separated Borel-set indicator is continuous at each interior-side mark
-- statement:
--   For an arbitrary real mark set B, its real indicator is continuous at any x lying in the interior of B or the interior of its complement. This is the exact local boundary-exclusion certificate for applying P2-L's finite and full cadlag mesh test convergence to Borel indicators; no assertion is made at boundary marks.

import Mathlib

open Set Filter Topology

theorem AvramDividend.Classical.avram_p2_l_mesh_indicator_continuous_at_interior_side (B : Set ℝ) (x : ℝ)
    (h : x ∈ interior B ∨ x ∈ interior (Bᶜ)) :
    ContinuousAt (B.indicator (fun _ : ℝ => (1 : ℝ))) x := by sorry
