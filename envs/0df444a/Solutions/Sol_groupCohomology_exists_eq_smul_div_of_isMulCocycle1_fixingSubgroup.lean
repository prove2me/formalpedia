-- Prove2me | solution 1 for groupCohomology.exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/901c09f3-ff8d-5610-b9b6-506607428a37

import Mathlib
import Theorems.Thm_groupCohomology_isMulCoboundary1_of_isMulCocycle1_of_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup

set_option autoImplicit false

universe u v

p2m_open "groupCohomology P2MW.S_groupCohomology_exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup.groupCohomology"

namespace groupCohomology
p2m_export "groupCohomology" "IsMulCocycle₁ isMulCoboundary1_of_isMulCocycle1_of_level"
p2m_open "groupCohomology"

private theorem fixingSubgroupEquiv_smul_units'
    {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    (σ : K.fixingSubgroup) (x : Ωˣ) :
    (IntermediateField.fixingSubgroupEquiv K σ) • x = (σ : Ω ≃ₐ[k] Ω) • x :=
  Units.ext rfl

end groupCohomology

theorem solution
    {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K]
    {f : K.fixingSubgroup → Ωˣ} (hf : IsMulCocycle₁ f)
    (hlc : ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧
      ∀ σ τ : K.fixingSubgroup, (τ : Ω ≃ₐ[k] Ω) ∈ L.fixingSubgroup → f (σ * τ) = f σ) :
    ∃ α : Ωˣ, ∀ σ : K.fixingSubgroup, f σ = (σ : Ω ≃ₐ[k] Ω) • α / α := by
  obtain ⟨L, hL, hinv⟩ := hlc
  haveI := hL
  let e := IntermediateField.fixingSubgroupEquiv K
  let f' : (Ω ≃ₐ[K] Ω) → Ωˣ := fun τ => f (e.symm τ)
  have hf' : IsMulCocycle₁ f' := by
    intro τ₁ τ₂
    show f (e.symm (τ₁ * τ₂)) = τ₁ • f (e.symm τ₂) * f (e.symm τ₁)
    rw [map_mul, hf, show ∀ (σ : K.fixingSubgroup) (x : Ωˣ), σ • x = (σ : Ω ≃ₐ[k] Ω) • x from
      fun _ _ => rfl, ← fixingSubgroupEquiv_smul_units', MulEquiv.apply_symm_apply]
  let E : IntermediateField K Ω := IntermediateField.extendScalars (le_sup_left : K ≤ K ⊔ L)
  haveI : FiniteDimensional k E := inferInstanceAs (FiniteDimensional k (↥(K ⊔ L)))
  haveI : FiniteDimensional K E := Module.Finite.of_restrictScalars_finite k K E
  have hlc' : ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ σ τ : Ω ≃ₐ[K] Ω, τ ∈ E.fixingSubgroup → f' (σ * τ) = f' σ := by
    refine ⟨E, inferInstance, fun σ τ hτ => ?_⟩
    show f (e.symm (σ * τ)) = f (e.symm σ)
    rw [map_mul]
    apply hinv
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hxE : x ∈ E := (IntermediateField.mem_extendScalars _).2 ((le_sup_right : L ≤ K ⊔ L) hx)
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x hxE
  obtain ⟨α, hα⟩ := isMulCoboundary1_of_isMulCocycle1_of_level hf' hlc'
  refine ⟨α, fun σ => ?_⟩
  rw [← fixingSubgroupEquiv_smul_units', hα (e σ)]
  show f (e.symm (e σ)) = f σ
  rw [MulEquiv.symm_apply_apply]

end S_groupCohomology_exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup
end P2MW
export P2MW.S_groupCohomology_exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup (solution)
