-- Prove2me | solution 1 for groupCohomology.cocycles1_conj_apply_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/db937e75-2e47-54e6-b8d9-fd8a12806f1a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_cocycles1_conj_apply_sub_eq

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem solution
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (c : cocycles₁ A) (g s : G) :
    A.ρ g (c (g⁻¹ * s * g)) - c s = A.ρ s (c g) - c g := by
  have hco := (mem_cocycles₁_iff (⇑c)).1 c.2
  have h1 : c (g⁻¹ * s * g) = A.ρ g⁻¹ (c (s * g)) + c g⁻¹ := by
    rw [mul_assoc]; exact hco g⁻¹ (s * g)
  have h2 : c (s * g) = A.ρ s (c g) + c s := hco s g
  rw [h1, map_add, h2, ← Module.End.mul_apply (A.ρ g) (A.ρ g⁻¹), ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply, cocycles₁_map_inv c g]
  abel

end S_groupCohomology_cocycles1_conj_apply_sub_eq
end P2MW
export P2MW.S_groupCohomology_cocycles1_conj_apply_sub_eq (solution)
