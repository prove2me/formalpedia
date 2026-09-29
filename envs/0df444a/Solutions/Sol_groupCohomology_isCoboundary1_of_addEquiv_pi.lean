-- Prove2me | solution 1 for groupCohomology.isCoboundary1_of_addEquiv_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9b092569-6fdf-52b8-9dcb-2ccd4d699f6a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_isCoboundary1_of_addEquiv_pi

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000
open groupCohomology

theorem solution
    {G P P₀ : Type*} [Group G] [AddCommGroup P] [AddCommGroup P₀] [SMul G P]
    (e : P ≃+ (G → P₀)) (he : ∀ (h : G) (p : P) (x : G), e (h • p) x = e p (h⁻¹ * x))
    (f : G → P) (hf : IsCocycle₁ f) : IsCoboundary₁ f := by

  refine ⟨e.symm (fun x => e (f x⁻¹) 1), fun g => ?_⟩
  apply e.injective
  funext x
  rw [map_sub, e.apply_symm_apply, Pi.sub_apply, he, e.apply_symm_apply, mul_inv_rev, inv_inv]

  rw [hf x⁻¹ g, map_add, Pi.add_apply, he, inv_inv, mul_one, add_sub_cancel_right]

end S_groupCohomology_isCoboundary1_of_addEquiv_pi
end P2MW
export P2MW.S_groupCohomology_isCoboundary1_of_addEquiv_pi (solution)
