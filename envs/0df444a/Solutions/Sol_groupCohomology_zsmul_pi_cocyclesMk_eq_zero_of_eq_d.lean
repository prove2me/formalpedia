-- Prove2me | solution 1 for groupCohomology.zsmul_pi_cocyclesMk_eq_zero_of_eq_d
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/b6ad5393-7d81-579e-b925-521bca808362

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_zsmul_pi_cocyclesMk_eq_zero_of_eq_d

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem solution
    {G : Type} [Group G] (A : Rep.{0} ℤ G) (n : ℕ) (m : ℤ) (x : (Fin (n + 1) → G) → A)
    (hx : (inhomogeneousCochains.d A (n + 1)).hom x = 0) (y : (Fin n → G) → A)
    (h : m • x = (inhomogeneousCochains.d A n).hom y) :
    m • groupCohomology.π A (n + 1) (groupCohomology.cocyclesMk x hx) = 0 := by

  have hsm : m • groupCohomology.cocyclesMk x hx = groupCohomology.toCocycles A n (n + 1) y := by
    apply (ModuleCat.mono_iff_injective (groupCohomology.iCocycles A (n + 1))).mp inferInstance
    show (groupCohomology.iCocycles A (n + 1)).hom (m • groupCohomology.cocyclesMk x hx) =
      (groupCohomology.iCocycles A (n + 1)).hom (groupCohomology.toCocycles A n (n + 1) y)
    rw [map_zsmul]
    have h1 : (groupCohomology.iCocycles A (n + 1)).hom (groupCohomology.cocyclesMk x hx) = x := groupCohomology.iCocycles_mk x hx
    have h2 : (groupCohomology.iCocycles A (n + 1)).hom (groupCohomology.toCocycles A n (n + 1) y) = (inhomogeneousCochains.d A n).hom y := by
      have hti := (inhomogeneousCochains A).toCycles_i n (n + 1)
      rw [inhomogeneousCochains.d_def] at hti
      have := congrArg (fun T => (ModuleCat.Hom.hom T) y) hti
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
      exact this
    rw [h1, h2, h]
  have hπ : (groupCohomology.π A (n + 1)).hom (groupCohomology.toCocycles A n (n + 1) y) = 0 := by
    have := congrArg (fun T => (ModuleCat.Hom.hom T) y) ((inhomogeneousCochains A).toCycles_comp_homologyπ n (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at this
    exact this
  show m • (groupCohomology.π A (n + 1)).hom (groupCohomology.cocyclesMk x hx) = 0
  rw [← map_zsmul, hsm, hπ]

end S_groupCohomology_zsmul_pi_cocyclesMk_eq_zero_of_eq_d
end P2MW
export P2MW.S_groupCohomology_zsmul_pi_cocyclesMk_eq_zero_of_eq_d (solution)
