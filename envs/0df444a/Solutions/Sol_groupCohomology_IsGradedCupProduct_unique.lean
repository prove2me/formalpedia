-- Prove2me | solution 1 for groupCohomology.IsGradedCupProduct.unique
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/8bf23a06-fe42-5a6a-bea8-c67f92a46ae6

import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Theorems.Thm_groupCohomology_d_cochainCup_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_IsGradedCupProduct_unique

set_option autoImplicit false
universe u
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory groupCohomology"

namespace P2mS26CupU

variable {k G : Type u} [CommRing k] [Group G]

theorem d_iCocycles (A : Rep.{u} k G) (n : ℕ) (x : cocycles A n) :
    (inhomogeneousCochains.d A n).hom ((iCocycles A n).hom x) = 0 := by
  have := congrArg (fun φ => φ.hom x) ((inhomogeneousCochains A).iCycles_d n (n + 1))
  simpa [ModuleCat.hom_comp] using this

theorem d_cup_eq_zero (A B : Rep.{u} k G) (p q : ℕ) (x : cocycles A p) (y : cocycles B q) :
    (inhomogeneousCochains.d (A ⊗ B) (p + q)).hom
      (cochainCup A B p q ((iCocycles A p).hom x) ((iCocycles B q).hom y)) = 0 := by
  funext σ
  rw [groupCohomology.d_cochainCup_apply, d_iCocycles, d_iCocycles, map_zero, map_zero, LinearMap.zero_apply,
    Pi.zero_apply, Pi.zero_apply, smul_zero, add_zero]

theorem π_surjective (A : Rep.{u} k G) (n : ℕ) : Function.Surjective (groupCohomology.π A n).hom :=
  (ModuleCat.epi_iff_surjective ((inhomogeneousCochains A).homologyπ n)).1 inferInstance

end P2mS26CupU

open P2mS26CupU in
theorem solution {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G)
    (cup cup' : groupCohomology.GradedCupFamily A B)
    (h : groupCohomology.IsGradedCupProduct A B cup) (h' : groupCohomology.IsGradedCupProduct A B cup') : cup = cup' := by
  funext p q
  refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
  obtain ⟨x, rfl⟩ := π_surjective A p a
  obtain ⟨y, rfl⟩ := π_surjective B q b
  rw [h.compat p q x y (d_cup_eq_zero A B p q x y), h'.compat p q x y (d_cup_eq_zero A B p q x y)]

end S_groupCohomology_IsGradedCupProduct_unique
end P2MW
export P2MW.S_groupCohomology_IsGradedCupProduct_unique (solution)
