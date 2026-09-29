-- Prove2me | solution 1 for groupCohomology.exists_linearMap_H2_continuousH2_ofAlgebraAutOnUnits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/32be01b9-e6cf-5348-8701-483859569bc7

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Theorems.Thm_groupCohomology_unitsInflate2_mem_levelCocycles2
import Theorems.Thm_groupCohomology_unitsInflate2_mem_levelCoboundaries2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_linearMap_H2_continuousH2_ofAlgebraAutOnUnits

set_option autoImplicit false

open CategoryTheory groupCohomology

set_option maxHeartbeats 1600000 in
theorem solution
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (L : IntermediateField K Ω) [Normal K L]
    (hL : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ L.fixingSubgroup) :
    ∃ inf : H2 (Rep.ofAlgebraAutOnUnits K L) →ₗ[ℤ] continuousH2 r (Rep.ofAlgebraAutOnUnits K Ω),
      ∀ (f : cocycles₂ (Rep.ofAlgebraAutOnUnits K L))
        (hf' : unitsInflate₂ L f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω)),
        inf (H2π (Rep.ofAlgebraAutOnUnits K L) f) =
          continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) ⟨unitsInflate₂ L f, hf'⟩ := by

  let Φ : cocycles₂ (Rep.ofAlgebraAutOnUnits K L) →ₗ[ℤ] levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω) :=
    ((unitsInflate₂ L).comp (cocycles₂ (Rep.ofAlgebraAutOnUnits K L)).subtype).codRestrict _
      fun f => unitsInflate2_mem_levelCocycles2 r L hL f.2

  have hker : LinearMap.range (shortComplexH2 (Rep.ofAlgebraAutOnUnits K L)).moduleCatToCycles ≤
      LinearMap.ker (continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) ∘ₗ Φ) := by
    rintro x ⟨y, rfl⟩
    exact (continuousH2π_eq_zero_iff r _ _).2 (unitsInflate2_mem_levelCoboundaries2 r L hL ⟨y, rfl⟩)
  refine ⟨(Submodule.liftQ _ (continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) ∘ₗ Φ) hker) ∘ₗ
      (H2Iso (Rep.ofAlgebraAutOnUnits K L)).hom.hom, fun f hf' => ?_⟩

  have h := π_comp_H2Iso_hom_apply (Rep.ofAlgebraAutOnUnits K L)
    ((isoCocycles₂ (Rep.ofAlgebraAutOnUnits K L)).inv f)
  simp only [Iso.inv_hom_id_apply] at h
  have e : (H2Iso (Rep.ofAlgebraAutOnUnits K L)).hom.hom (H2π _ f)
      = (LinearMap.range (shortComplexH2 (Rep.ofAlgebraAutOnUnits K L)).moduleCatToCycles).mkQ f :=
    Eq.trans rfl h
  have key : ∀ z, z = (LinearMap.range (shortComplexH2 (Rep.ofAlgebraAutOnUnits K L)).moduleCatToCycles).mkQ f →
      (Submodule.liftQ _ (continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) ∘ₗ Φ) hker) z
        = continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) ⟨unitsInflate₂ L f, hf'⟩ := by
    rintro _ rfl; rfl
  exact key _ e

end S_groupCohomology_exists_linearMap_H2_continuousH2_ofAlgebraAutOnUnits
end P2MW
export P2MW.S_groupCohomology_exists_linearMap_H2_continuousH2_ofAlgebraAutOnUnits (solution)
