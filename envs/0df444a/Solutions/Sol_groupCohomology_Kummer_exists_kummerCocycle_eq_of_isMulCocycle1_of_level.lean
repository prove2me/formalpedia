-- Prove2me | solution 1 for groupCohomology.Kummer.exists_kummerCocycle_eq_of_isMulCocycle1_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/01121675-fe84-5dac-92a9-bf2467c12d3f

import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_of_level

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L] {p : ℕ} [NeZero p]
    {f : (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₁ f) (hfp : ∀ σ, f σ ^ p = 1)
    (hlc : ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      ∀ σ τ : L ≃ₐ[K] L, τ ∈ E.fixingSubgroup → f (σ * τ) = f σ) :
    ∃ (a : Kˣ) (α : Lˣ),
      algebraMap K L (a : K) = (α : L) ^ p ∧ ∀ σ : L ≃ₐ[K] L, f σ = kummerCocycle α σ := by
  classical
  obtain ⟨E, hE, hinv⟩ := hlc
  haveI := hE

  let S : Set L := Set.range (fun ζ : rootsOfUnity p L => ((ζ : Lˣ) : L))
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

  have hfN : ∀ σ, (f σ : L) ∈ N := fun σ =>
    hSN (IntermediateField.subset_adjoin K S ⟨⟨f σ, (mem_rootsOfUnity p (f σ)).2 (hfp σ)⟩, rfl⟩)

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
    rw [hfN_val, Units.val_mul, map_mul, hact, hfN_val, hfN_val, hf σ₁ σ₂, Units.val_mul,
      val_smul_units]
  have hgp : ∀ τ, g τ ^ p = 1 := by
    intro τ
    apply key
    rw [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one]
    show (algebraMap N L ((fN (sec τ) : (↥N)ˣ) : N)) ^ p = 1
    rw [hfN_val, ← Units.val_pow_eq_pow_val, hfp, Units.val_one]

  obtain ⟨a, β, hβ, hgβ⟩ := exists_kummerCocycle_eq_of_isMulCocycle1 hgc hgp
  refine ⟨a, Units.map (algebraMap N L : N →* L) β, ?_, fun σ => ?_⟩
  · rw [Units.coe_map, MonoidHom.coe_coe, ← map_pow, ← hβ, ← IsScalarTower.algebraMap_apply]
  · ext
    rw [← hfN_val σ, ← hg, hgβ (res σ), kummerCocycle_apply, kummerCocycle_apply,
      Units.val_div_eq_div_val, map_div₀, hact, Units.val_div_eq_div_val, val_smul_units,
      Units.coe_map, MonoidHom.coe_coe]

end S_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_of_level
end P2MW
export P2MW.S_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_of_level (solution)
