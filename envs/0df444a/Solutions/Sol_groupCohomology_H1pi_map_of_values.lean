-- Prove2me | solution 1 for groupCohomology.H1pi_map_of_values
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:12.993403+00:00
-- url     : https://prove2.me/submissions/a3adfb7c-3e66-45ff-ac4b-59743571c40f

import Mathlib

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

/-- Cohomology functoriality evaluated on the concrete one-cocycle carrier. -/
theorem _root_.solution
    {k G H : Type} [CommRing k] [Group G] [Group H]
    (r : H →* G) (A : Rep k G) (B : Rep k H)
    (φ : Rep.res r A ⟶ B) (c : cocycles₁ A) (d : cocycles₁ B)
    (h : ∀ σ, φ.hom (c (r σ)) = d σ) :
    (groupCohomology.map r φ 1).hom (H1π A c) = H1π B d := by
  change (groupCohomology.map r φ 1).hom ((π A 1).hom ((isoCocycles₁ A).inv c)) =
    (π B 1).hom ((isoCocycles₁ B).inv d)
  rw [π_map_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective (iCocycles B 1)).1 inferInstance
  change ((cocyclesMap r φ 1 ≫ iCocycles B 1).hom ((isoCocycles₁ A).inv c)) = _
  rw [HomologicalComplex.cyclesMap_i]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [isoCocycles₁_inv_comp_iCocycles_apply, isoCocycles₁_inv_comp_iCocycles_apply]
  apply inhomogeneousCochains.ext
  intro σ
  exact h (σ 0)

end groupCohomology
