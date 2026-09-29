-- Prove2me | solution 1 for groupCohomology.exists_isGalois_of_isLevelConstant1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/76b58d84-2003-52d9-b81e-8d25cae7ca20

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_isGalois_of_isLevelConstant1

set_option autoImplicit false

universe u

namespace P2mS26U1

open IntermediateField

variable {G : Type*} [Group G]

theorem comap_fixingSubgroup_eq_ker (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    F.fixingSubgroup.comap r
      = ((AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).comp r).ker := by
  rw [← @IntermediateField.restrictNormalHom_ker ℚ (AlgebraicClosure ℚ) _ _ _ F ‹Normal ℚ F›,
    MonoidHom.comap_ker]
  rfl

theorem normal_comap_fixingSubgroup (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    (F.fixingSubgroup.comap r).Normal := by
  rw [comap_fixingSubgroup_eq_ker]; exact MonoidHom.normal_ker _

theorem finiteIndex_comap_fixingSubgroup (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F] :
    (F.fixingSubgroup.comap r).FiniteIndex := by
  rw [comap_fixingSubgroup_eq_ker]; exact Subgroup.finiteIndex_ker _

end P2mS26U1

namespace P2mS26U1

theorem exists_isGalois_ge (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F' ∧ IsGalois ℚ F' ∧ F ≤ F' := by
  haveI : Normal ℚ (AlgebraicClosure ℚ) := by
    convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) inferInstance
    rfl
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ L := normalClosure.is_finiteDimensional ℚ F (AlgebraicClosure ℚ)
  haveI : Normal ℚ L := normalClosure.normal ℚ F (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ L := ⟨⟩
  exact ⟨L, inferInstance, inferInstance, IntermediateField.le_normalClosure F⟩

end P2mS26U1

theorem solution {G : Type u} [Group G]
    {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} {X : Type*} {f : G → X}
    (hf : groupCohomology.IsLevelConstant₁ r f) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      ∀ g s : G, r s ∈ F.fixingSubgroup → f (g * s) = f g ∧ f (s * g) = f g := by
  obtain ⟨F₀, hF₀, h⟩ := hf
  haveI := hF₀
  obtain ⟨F, hF, hG, hle⟩ := P2mS26U1.exists_isGalois_ge F₀
  haveI := hG
  have hN := P2mS26U1.normal_comap_fixingSubgroup r F
  refine ⟨F, hF, hG, fun g s hs => ⟨h g s (IntermediateField.fixingSubgroup_antitone hle hs), ?_⟩⟩
  have hs' : g⁻¹ * s * g ∈ F.fixingSubgroup.comap r := by
    simpa using hN.conj_mem s hs g⁻¹
  have := h g (g⁻¹ * s * g) (IntermediateField.fixingSubgroup_antitone hle hs')
  rwa [show g * (g⁻¹ * s * g) = s * g by group] at this

end S_groupCohomology_exists_isGalois_of_isLevelConstant1
end P2MW
export P2MW.S_groupCohomology_exists_isGalois_of_isLevelConstant1 (solution)
