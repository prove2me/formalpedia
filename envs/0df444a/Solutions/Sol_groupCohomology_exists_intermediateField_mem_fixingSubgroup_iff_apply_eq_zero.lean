-- Prove2me | solution 1 for groupCohomology.exists_intermediateField_mem_fixingSubgroup_iff_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/8c239c0d-d26c-5e1c-9f14-902b4f7a78b1

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_intermediateField_mem_fixingSubgroup_iff_apply_eq_zero

set_option autoImplicit false
set_option maxHeartbeats 1600000
open CategoryTheory

open groupCohomology

theorem solution
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (p : ℕ) [Fact p.Prime]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (χ : (Ω ≃ₐ[K] Ω) → ZMod p) (hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ)
    (hχlc : IsLevelConstant₁ r χ) (hχ0 : ∃ σ, χ σ ≠ 0) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧ IsGalois K E ∧ Module.finrank K E = p ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup ↔ χ σ = 0 := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Normal K Ω := inferInstance

  let χm : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod p) :=
    { toFun := fun σ => Multiplicative.ofAdd (χ σ)
      map_one' := by
        have h := hχ 1 1
        rw [mul_one] at h
        have h0 : χ 1 = 0 := by
          have : χ 1 + χ 1 = χ 1 + 0 := by rw [add_zero, ← h]
          exact add_left_cancel this
        show Multiplicative.ofAdd (χ 1) = 1
        rw [h0]; rfl
      map_mul' := fun σ τ => by
        show Multiplicative.ofAdd (χ (σ * τ)) = Multiplicative.ofAdd (χ σ) * Multiplicative.ofAdd (χ τ)
        rw [hχ, ofAdd_add] }
  have hχm : ∀ σ, χm σ = Multiplicative.ofAdd (χ σ) := fun _ => rfl
  have hker : ∀ σ, σ ∈ χm.ker ↔ χ σ = 0 := fun σ => by
    rw [MonoidHom.mem_ker, hχm]
    exact ⟨fun h => Multiplicative.ofAdd.injective h, fun h => by rw [h]; rfl⟩

  obtain ⟨F, hF, hFχ⟩ := hχlc
  haveI := hF
  obtain ⟨E₁, hE₁, hE₁F⟩ := hopen F hF
  haveI := hE₁
  have hχE₁ : ∀ σ, σ ∈ E₁.fixingSubgroup → χ σ = 0 := by
    intro σ hσ
    have h1 : χ 1 = 0 := (hker 1).1 χm.ker.one_mem
    have := hFχ 1 σ (hE₁F σ hσ)
    rwa [one_mul, h1] at this
  let E₀ : IntermediateField K Ω := IntermediateField.normalClosure K E₁ Ω
  haveI : FiniteDimensional K E₀ := normalClosure.is_finiteDimensional K E₁ Ω
  haveI : Normal K E₀ := normalClosure.normal K E₁ Ω
  haveI : Algebra.IsSeparable K E₀ := Algebra.isSeparable_tower_bot_of_isSeparable K E₀ Ω
  haveI : IsGalois K E₀ := ⟨⟩
  have hE₁E₀ : E₁ ≤ E₀ := IntermediateField.le_normalClosure E₁

  let res : (Ω ≃ₐ[K] Ω) →* (E₀ ≃ₐ[K] E₀) := AlgEquiv.restrictNormalHom E₀
  have hres : Function.Surjective res := AlgEquiv.restrictNormalHom_surjective Ω
  have hkerres : res.ker = E₀.fixingSubgroup := IntermediateField.restrictNormalHom_ker E₀
  have hle : res.ker ≤ χm.ker := by
    intro σ hσ
    rw [hkerres] at hσ
    exact (hker σ).2 (hχE₁ σ (IntermediateField.fixingSubgroup_antitone hE₁E₀ hσ))
  let χ₀ : (E₀ ≃ₐ[K] E₀) →* Multiplicative (ZMod p) :=
    (QuotientGroup.lift res.ker χm hle).comp (QuotientGroup.quotientKerEquivOfSurjective res hres).symm.toMonoidHom
  have hχ₀ : ∀ σ, χ₀ (res σ) = χm σ := by
    intro σ
    show QuotientGroup.lift res.ker χm hle ((QuotientGroup.quotientKerEquivOfSurjective res hres).symm (res σ)) = χm σ
    have : (QuotientGroup.quotientKerEquivOfSurjective res hres).symm (res σ) = (σ : (Ω ≃ₐ[K] Ω) ⧸ res.ker) := by
      rw [MulEquiv.symm_apply_eq]; rfl
    rw [this]; rfl

  let H : Subgroup (E₀ ≃ₐ[K] E₀) := χ₀.ker
  haveI : H.Normal := MonoidHom.normal_ker χ₀
  let E' : IntermediateField K E₀ := IntermediateField.fixedField H
  haveI : IsGalois K E' := IsGalois.of_fixedField_normal_subgroup H
  let E : IntermediateField K Ω := IntermediateField.lift E'
  let eE : E' ≃ₐ[K] E := IntermediateField.liftAlgEquiv E'
  haveI : FiniteDimensional K E' := inferInstance
  haveI : FiniteDimensional K E := LinearEquiv.finiteDimensional eE.toLinearEquiv
  haveI : IsGalois K E := IsGalois.of_algEquiv eE

  have hχ₀surj : Function.Surjective χ₀ := by
    obtain ⟨σ₀, hσ₀⟩ := hχ0
    have hne : χ₀ (res σ₀) ≠ 1 := by
      rw [hχ₀, hχm]
      exact fun h => hσ₀ (Multiplicative.ofAdd.injective h)
    haveI : Fact (Nat.card (Multiplicative (ZMod p))).Prime := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]; exact ⟨hp⟩
    have htop : χ₀.range = ⊤ := by
      refine (Subgroup.eq_bot_or_eq_top_of_prime_card χ₀.range).resolve_left ?_
      intro hbot
      apply hne
      have : χ₀ (res σ₀) ∈ χ₀.range := ⟨res σ₀, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    exact MonoidHom.range_eq_top.1 htop
  refine ⟨E, inferInstance, inferInstance, ?_, fun σ => ?_⟩
  ·
    have h1 : Module.finrank K E = Module.finrank K E' := (LinearEquiv.finrank_eq eE.toLinearEquiv).symm
    have h2 : Module.finrank E' E₀ = Nat.card H := IntermediateField.finrank_fixedField_eq_card H
    have h3 : Nat.card (E₀ ≃ₐ[K] E₀) = Module.finrank K E₀ := IsGalois.card_aut_eq_finrank K E₀
    have h4 : Module.finrank K E' * Module.finrank E' E₀ = Module.finrank K E₀ := Module.finrank_mul_finrank K E' E₀
    have h5 : Nat.card (E₀ ≃ₐ[K] E₀) = Nat.card H * Nat.card (Multiplicative (ZMod p)) := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective χ₀ hχ₀surj).toEquiv]
      exact (Subgroup.card_eq_card_quotient_mul_card_subgroup H).trans (mul_comm _ _)
    have h6 : Nat.card (Multiplicative (ZMod p)) = p := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    have hH : 0 < Nat.card H := Nat.card_pos
    rw [h1]
    rw [h2] at h4
    rw [h6, h3] at h5
    rw [h5] at h4

    have := Nat.eq_of_mul_eq_mul_right hH (h4.trans (mul_comm _ _))
    exact this
  ·
    have key : σ ∈ E.fixingSubgroup ↔ res σ ∈ E'.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
      constructor
      · intro h x hx
        apply Subtype.ext
        have hxE : (x : Ω) ∈ E := (IntermediateField.mem_lift x).2 hx
        have := h x hxE
        rw [← this]
        exact AlgEquiv.restrictNormal_commutes σ E₀ x
      · rintro h _ ⟨x, hx, rfl⟩
        have := congrArg (fun y : E₀ => (y : Ω)) (h x hx)
        show σ (x : Ω) = (x : Ω)
        exact (AlgEquiv.restrictNormal_commutes σ E₀ x).symm.trans this
    rw [key, IntermediateField.fixingSubgroup_fixedField H, ← hker, MonoidHom.mem_ker, MonoidHom.mem_ker, ← hχ₀]

end S_groupCohomology_exists_intermediateField_mem_fixingSubgroup_iff_apply_eq_zero
end P2MW
export P2MW.S_groupCohomology_exists_intermediateField_mem_fixingSubgroup_iff_apply_eq_zero (solution)
