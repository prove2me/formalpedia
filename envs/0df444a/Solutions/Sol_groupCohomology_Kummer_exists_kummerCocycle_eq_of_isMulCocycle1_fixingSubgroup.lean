-- Prove2me | solution 1 for groupCohomology.Kummer.exists_kummerCocycle_eq_of_isMulCocycle1_fixingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/c829dd98-bee9-5f60-8c2b-93d36bd69f11

import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_of_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_fixingSubgroup

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

private theorem fixingSubgroupEquiv_smul_units
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    (σ : K.fixingSubgroup) (x : Ωˣ) :
    (IntermediateField.fixingSubgroupEquiv K σ) • x = (σ : Ω ≃ₐ[k] Ω) • x :=
  Units.ext rfl

private theorem kummerCocycle_fixingSubgroupEquiv
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    (α : Ωˣ) (σ : K.fixingSubgroup) :
    kummerCocycle α (IntermediateField.fixingSubgroupEquiv K σ) = kummerCocycle α (σ : Ω ≃ₐ[k] Ω) := by
  rw [kummerCocycle_apply, kummerCocycle_apply, fixingSubgroupEquiv_smul_units]

private theorem fixingSubgroup_smul_units
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    (σ : K.fixingSubgroup) (x : Ωˣ) : σ • x = (σ : Ω ≃ₐ[k] Ω) • x := rfl

theorem solution
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] {p : ℕ} [NeZero p]
    {f : K.fixingSubgroup → Ωˣ} (hf : IsMulCocycle₁ f) (hfp : ∀ σ, f σ ^ p = 1)
    (hlc : ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧
      ∀ σ τ : K.fixingSubgroup, (τ : Ω ≃ₐ[k] Ω) ∈ L.fixingSubgroup → f (σ * τ) = f σ) :
    ∃ (a : Kˣ) (α : Ωˣ), algebraMap K Ω (a : K) = (α : Ω) ^ p ∧
      ∀ σ : K.fixingSubgroup, f σ = kummerCocycle α (σ : Ω ≃ₐ[k] Ω) := by
  obtain ⟨L, hL, hinv⟩ := hlc
  haveI := hL
  let e := IntermediateField.fixingSubgroupEquiv K
  let f' : (Ω ≃ₐ[K] Ω) → Ωˣ := fun τ => f (e.symm τ)
  have hf' : IsMulCocycle₁ f' := by
    intro τ₁ τ₂
    show f (e.symm (τ₁ * τ₂)) = τ₁ • f (e.symm τ₂) * f (e.symm τ₁)
    rw [map_mul, hf, fixingSubgroup_smul_units, ← fixingSubgroupEquiv_smul_units,
      MulEquiv.apply_symm_apply]
  have hfp' : ∀ τ, f' τ ^ p = 1 := fun τ => hfp _

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
  obtain ⟨a, α, hα, hfa⟩ := exists_kummerCocycle_eq_of_isMulCocycle1_of_level hf' hfp' hlc'
  refine ⟨a, α, hα, fun σ => ?_⟩
  have h := hfa (e σ)
  rw [kummerCocycle_fixingSubgroupEquiv] at h
  rw [← h]
  show f σ = f (e.symm (e σ))
  rw [MulEquiv.symm_apply_apply]

end S_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_fixingSubgroup
end P2MW
export P2MW.S_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_fixingSubgroup (solution)
