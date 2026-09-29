-- Prove2me | solution 1 for groupCohomology.cocycles1_apply_eq_zero_of_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9b16afdc-a5f3-5b5d-ae1c-8b488aae49d5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_cocycles1_apply_eq_zero_of_mem_closure

open CategoryTheory Module groupCohomology

universe u

theorem solution {k G : Type u} [CommRing k] [Group G] {M : Rep k G} (c : cocycles₁ M) {s : Set G}
    (hs : ∀ g ∈ s, c g = 0) {g : G} (hg : g ∈ Subgroup.closure s) : c g = 0 := by
  have hcoc := (mem_cocycles₁_iff (A := M) ⇑c).1 c.2
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => exact cocycles₁_map_one c
  | mul x y _ _ hx hy => rw [hcoc x y, hy, map_zero, zero_add, hx]
  | inv x _ hx =>
      have h := hcoc x⁻¹ x
      rw [inv_mul_cancel, cocycles₁_map_one, hx, map_zero, zero_add] at h
      exact h.symm

end S_groupCohomology_cocycles1_apply_eq_zero_of_mem_closure
end P2MW
export P2MW.S_groupCohomology_cocycles1_apply_eq_zero_of_mem_closure (solution)
