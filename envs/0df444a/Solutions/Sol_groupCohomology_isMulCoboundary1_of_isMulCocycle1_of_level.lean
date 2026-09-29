-- Prove2me | solution 1 for groupCohomology.isMulCoboundary1_of_isMulCocycle1_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/877b6aa1-2513-5d89-b621-1c37dfdff83c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_isMulCoboundary1_of_isMulCocycle1_of_level

set_option autoImplicit false

universe u v

p2m_open "groupCohomology P2MW.S_groupCohomology_isMulCoboundary1_of_isMulCocycle1_of_level.groupCohomology"

namespace groupCohomology
p2m_export "groupCohomology" "IsMulCoboundary₁ isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units map IsMulCocycle₁"
p2m_open "groupCohomology"

private theorem finiteIndex_fixingSubgroup_of_finiteDimensional {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (E : IntermediateField K L) [FiniteDimensional K E] : E.fixingSubgroup.FiniteIndex := by
  let φ : (L ≃ₐ[K] L) ⧸ E.fixingSubgroup → E →ₐ[K] L := Quotient.lift
    (fun f ↦ f.toAlgHom.comp E.val)
    (by rintro _ τ ⟨σ, rfl⟩; ext x; exact DFunLike.congr_arg τ (σ.2 x))
  have hφ : Function.Injective φ := by
    rintro ⟨σ⟩ ⟨τ⟩ (H : σ.toAlgHom.comp E.val = τ.toAlgHom.comp E.val)
    refine Quotient.sound ⟨⟨.op (τ⁻¹ * σ), fun x ↦ ?_⟩, by simp⟩
    simpa [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] using DFunLike.congr_fun H x
  have := Finite.of_injective _ hφ
  exact Subgroup.finiteIndex_of_finite_quotient

end groupCohomology

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {f : (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₁ f)
    (hlc : ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      ∀ σ τ : L ≃ₐ[K] L, τ ∈ E.fixingSubgroup → f (σ * τ) = f σ) :
    IsMulCoboundary₁ f := by
  classical
  obtain ⟨E, hE, hinv⟩ := hlc
  haveI := hE
  haveI : E.fixingSubgroup.FiniteIndex := finiteIndex_fixingSubgroup_of_finiteDimensional E
  haveI : Finite ((L ≃ₐ[K] L) ⧸ E.fixingSubgroup) := Subgroup.finite_quotient_of_finiteIndex

  let S : Set L := Set.range (fun q : (L ≃ₐ[K] L) ⧸ E.fixingSubgroup => ((f q.out : Lˣ) : L))
  haveI : Finite S := (Set.finite_range _).to_subtype
  haveI : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let E' : IntermediateField K L := E ⊔ IntermediateField.adjoin K S
  let N : IntermediateField K L := IntermediateField.normalClosure K E' L
  haveI : Algebra.IsSeparable K N := Algebra.isSeparable_tower_bot_of_isSeparable K N L
  haveI : IsGalois K N := IsGalois.mk
  letI instN : MulDistribMulAction (N ≃ₐ[K] N) (↥N)ˣ := AlgEquiv.instMulDistribMulActionUnits
  have hEN : E ≤ N := le_sup_left.trans (IntermediateField.le_normalClosure E')
  have hSN : IntermediateField.adjoin K S ≤ N :=
    le_sup_right.trans (IntermediateField.le_normalClosure E')

  have hfN : ∀ σ, (f σ : L) ∈ N := by
    intro σ
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul E.fixingSubgroup σ
    have hval : f ((QuotientGroup.mk σ : (L ≃ₐ[K] L) ⧸ E.fixingSubgroup).out) = f σ := by
      rw [hh, hinv σ h h.2]
    exact hSN (IntermediateField.subset_adjoin K S ⟨QuotientGroup.mk σ, congrArg (fun x : Lˣ => (x : L)) hval⟩)

  have hinvN : ∀ σ τ : L ≃ₐ[K] L, τ ∈ N.fixingSubgroup → f (σ * τ) = f σ := fun σ τ hτ =>
    hinv σ τ (IntermediateField.fixingSubgroup_antitone hEN hτ)
  have key : ∀ {x y : (↥N)ˣ}, algebraMap N L (x : N) = algebraMap N L (y : N) → x = y :=
    fun h => Units.ext ((algebraMap N L).injective h)

  let res : (L ≃ₐ[K] L) →* (N ≃ₐ[K] N) := AlgEquiv.restrictNormalHom N
  have hres : Function.Surjective res := AlgEquiv.restrictNormalHom_surjective L
  let sec : (N ≃ₐ[K] N) → (L ≃ₐ[K] L) := Function.surjInv hres
  have hsec : ∀ τ, res (sec τ) = τ := Function.surjInv_eq hres
  let fN : (L ≃ₐ[K] L) → (↥N)ˣ := fun σ =>
    Units.mk0 ⟨(f σ : L), hfN σ⟩ (fun h => (f σ).ne_zero (congrArg Subtype.val h))
  have hfN_val : ∀ σ, algebraMap N L (fN σ : N) = f σ := fun σ => rfl
  have hfN_res : ∀ σ σ' : L ≃ₐ[K] L, res σ = res σ' → fN σ = fN σ' := by
    intro σ σ' h
    have hker : σ⁻¹ * σ' ∈ N.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker N, MonoidHom.mem_ker, map_mul, map_inv, h,
        inv_mul_cancel]
    have hσσ' : f σ' = f σ := by
      have := hinvN σ (σ⁻¹ * σ') hker
      rwa [mul_inv_cancel_left] at this
    apply key
    rw [hfN_val, hfN_val, hσσ']
  let g : (N ≃ₐ[K] N) → (↥N)ˣ := fun τ => fN (sec τ)
  have hg : ∀ σ, g (res σ) = fN σ := fun σ => hfN_res _ _ (hsec (res σ))
  have hact : ∀ (σ : L ≃ₐ[K] L) (x : (↥N)ˣ),
      algebraMap N L ((res σ • x : (↥N)ˣ) : N) = σ (algebraMap N L (x : N)) := fun σ x =>
    AlgEquiv.restrictNormalHom_apply N σ (x : N)

  have hgc : IsMulCocycle₁ g := by
    intro τ₁ τ₂
    obtain ⟨σ₁, rfl⟩ := hres τ₁
    obtain ⟨σ₂, rfl⟩ := hres τ₂
    rw [← map_mul, hg, hg, hg]
    apply key
    rw [hfN_val, Units.val_mul, map_mul, hact, hfN_val, hfN_val, hf σ₁ σ₂, Units.val_mul]
    rfl

  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units g hgc
  refine ⟨Units.map (algebraMap N L : N →* L) β, fun σ => ?_⟩
  ext
  have hsm : ∀ (τ : L ≃ₐ[K] L) (x : Lˣ), ((τ • x : Lˣ) : L) = τ (x : L) := fun _ _ => rfl
  rw [← hfN_val σ, ← hg, ← hβ (res σ), Units.val_div_eq_div_val, Units.val_div_eq_div_val,
    map_div₀, hact, hsm, Units.coe_map, MonoidHom.coe_coe]

end S_groupCohomology_isMulCoboundary1_of_isMulCocycle1_of_level
end P2MW
export P2MW.S_groupCohomology_isMulCoboundary1_of_isMulCocycle1_of_level (solution)
