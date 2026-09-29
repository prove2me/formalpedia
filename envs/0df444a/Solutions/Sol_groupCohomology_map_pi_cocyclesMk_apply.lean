-- Prove2me | solution 1 for groupCohomology.map_pi_cocyclesMk_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a1d583e4-59e1-5211-84ad-ccff452d8184

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_map_pi_cocyclesMk_apply

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem solution
    {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep.{0} k H} {B : Rep.{0} k G}
    (f : G →* H) (φ : Rep.res f A ⟶ B) (n : ℕ) (x : (Fin n → H) → A)
    (hx : (inhomogeneousCochains.d A n).hom x = 0)
    (hx' : (inhomogeneousCochains.d B n).hom (fun g => φ.hom (x (f ∘ g))) = 0) :
    (groupCohomology.map f φ n).hom (groupCohomology.π A n (groupCohomology.cocyclesMk x hx)) =
      groupCohomology.π B n (groupCohomology.cocyclesMk (fun g => φ.hom (x (f ∘ g))) hx') := by
  rw [groupCohomology.π_map_apply]
  congr 1

  apply (ModuleCat.mono_iff_injective (iCocycles B n)).mp inferInstance
  rw [iCocycles_mk]
  have h1 : (cocyclesMap f φ n ≫ iCocycles B n) (cocyclesMk x hx) = ((iCocycles A n) ≫ (cochainsMap f φ).f n) (cocyclesMk x hx) := by
    rw [HomologicalComplex.cyclesMap_i]
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, iCocycles_mk] at h1
  rw [h1, cochainsMap_f]
  rfl

end S_groupCohomology_map_pi_cocyclesMk_apply
end P2MW
export P2MW.S_groupCohomology_map_pi_cocyclesMk_apply (solution)
