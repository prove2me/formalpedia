-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_mark_nearby_cuts
-- name    : AvramDividend.Classical.avram_p2_l_mesh_finite_mark_nearby_cuts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:37:08.181935+00:00
-- url     : https://prove2.me/theorems/658437d1-8afc-4a6d-a8ff-1f2bfe650c41
-- title:
--   Perturb every finite-mesh nominal cut away from marked jumps with a uniform error radius
-- statement:
--   For any finite set of actual intrinsic jump-mark values, any indexed family of nominal real partition cuts and positive radius, select all cuts within that radius of their nominal positions while avoiding the finite marked-jump set. The same radius works simultaneously for all indices, permitting uniform mesh-size control.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_mark_joint_avoiding_cuts

open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_finite_mark_nearby_cuts
    {ι : Type*} (S : Finset ℝ) (x : ι → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ y : ι → ℝ, ∀ i : ι, |y i - x i| < δ ∧ y i ∉ S := by sorry
