-- Prove2me | solution 1 for groupCohomology.isCoboundary2_of_addEquiv_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/1ddf1333-4925-551e-9996-f766e44fc530

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_isCoboundary2_of_addEquiv_pi

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000
open groupCohomology

theorem solution
    {G P P₀ : Type*} [Group G] [AddCommGroup P] [AddCommGroup P₀] [SMul G P]
    (e : P ≃+ (G → P₀)) (he : ∀ (h : G) (p : P) (x : G), e (h • p) x = e p (h⁻¹ * x))
    (f : G × G → P) (hf : IsCocycle₂ f) : IsCoboundary₂ f := by

  refine ⟨fun g => e.symm (fun y => e (f (y⁻¹, g)) 1), fun g h => ?_⟩
  apply e.injective
  funext y
  simp only [map_add, map_sub, e.apply_symm_apply, Pi.add_apply, Pi.sub_apply, he, mul_inv_rev, inv_inv]

  have hc' : f (y⁻¹ * g, h) - f (y⁻¹, g * h) + f (y⁻¹, g) = y⁻¹ • f (g, h) := by
    rw [sub_add_eq_add_sub, hf y⁻¹ g h, add_sub_cancel_right]
  have := congrArg (fun p => e p 1) hc'
  simp only [map_add, map_sub, Pi.add_apply, Pi.sub_apply, he, inv_inv, mul_one] at this
  exact this

end S_groupCohomology_isCoboundary2_of_addEquiv_pi
end P2MW
export P2MW.S_groupCohomology_isCoboundary2_of_addEquiv_pi (solution)
