-- Prove2me | solution 1 for groupCohomology.map_carryFun_adjoin_rootsOfUnity_eq_zero_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/e815b264-fce5-5df1-99a2-ba724b3c3441

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw
import Theorems.Thm_ExtCitation_LocalLevel_exists_relative_ramification_inertia_Rw
import Theorems.Thm_IntermediateField_exists_generator_frobenius_adjoin_rootsOfUnity_padic
import Theorems.Thm_IntermediateField_exists_uniformiser_padic
import Theorems.Thm_IntermediateField_exists_norm_eq_of_nnnorm_eq_one_adjoin_rootsOfUnity_padic
import Theorems.Thm_IntermediateField_finrank_adjoin_rootsOfUnity_padic_eq_orderOf
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_groupCohomology_carry_H2pi_eq_zero_iff
import Theorems.Thm_groupCohomology_map_carry_H2pi_eq_smul_carry
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_map_carryFun_adjoin_rootsOfUnity_eq_zero_of_dvd
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology
open scoped NNReal

namespace Ws26T4D
open ExtCitation.LocalLevel

variable (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

theorem mem_Rw_iff_norm_le_one (x : Kw) : x ∈ Rw q Kw ↔ ‖(x : PadicAlgCl q)‖ ≤ 1 := by
  rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, PadicAlgCl.valuation_def]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

theorem norm_coe_eq_spectralNorm (x : Kw) : ‖(x : PadicAlgCl q)‖ = spectralNorm ℚ_[q] Kw x := by
  rw [spectralNorm.eq_of_tower (L := PadicAlgCl q), PadicAlgCl.spectralNorm_eq]; rfl

end Ws26T4D

namespace Ws26L3
open ExtCitation.LocalLevel Ws26T4D

variable (q : ℕ) [Fact q.Prime] (F : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] F]

theorem norm_coe_unit_eq_one {x : Rw q F} (hx : IsUnit x) : ‖((x : F) : PadicAlgCl q)‖ = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h1 : ‖(((u : Rw q F) : F) : PadicAlgCl q)‖ ≤ 1 := (mem_Rw_iff_norm_le_one q F _).mp (u : Rw q F).2
  have h2 : ‖((((u⁻¹ : (Rw q F)ˣ) : Rw q F) : F) : PadicAlgCl q)‖ ≤ 1 :=
    (mem_Rw_iff_norm_le_one q F _).mp ((u⁻¹ : (Rw q F)ˣ) : Rw q F).2
  have hmul : ‖(((u : Rw q F) : F) : PadicAlgCl q)‖ * ‖((((u⁻¹ : (Rw q F)ˣ) : Rw q F) : F) : PadicAlgCl q)‖ = 1 := by
    rw [← norm_mul]
    have := congrArg (fun z : Rw q F => ((z : F) : PadicAlgCl q)) u.mul_inv
    push_cast at this
    rw [this, norm_one]
  by_contra hne
  have hlt := lt_of_le_of_ne h1 hne
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt h2
  linarith

theorem isUnit_of_norm_coe_eq_one {x : Rw q F} (hx : ‖((x : F) : PadicAlgCl q)‖ = 1) : IsUnit x := by
  have hx0 : (x : F) ≠ 0 := by
    intro h; rw [h] at hx; simp at hx
  have hinv : (x : F)⁻¹ ∈ Rw q F := by
    rw [mem_Rw_iff_norm_le_one]; push_cast; rw [norm_inv, hx, inv_one]
  exact isUnit_iff_exists_inv.mpr ⟨⟨(x : F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

set_option maxHeartbeats 6400000 in

theorem exists_unit_eq_pow_mul {π₀ y : F} (h0 : 0 < ‖(π₀ : PadicAlgCl q)‖) (h1 : ‖(π₀ : PadicAlgCl q)‖ < 1)
    {i : ℕ} (hy : ‖(y : PadicAlgCl q)‖ = ‖(π₀ : PadicAlgCl q)‖ ^ i) :
    ∃ (hπ : π₀ ∈ Rw q F) (hy' : y ∈ Rw q F) (w : (Rw q F)ˣ), (⟨y, hy'⟩ : Rw q F) = ⟨π₀, hπ⟩ ^ i * (w : Rw q F) := by
  have hπR : π₀ ∈ Rw q F := (mem_Rw_iff_norm_le_one q F _).mpr h1.le
  have hyR : y ∈ Rw q F := by
    rw [mem_Rw_iff_norm_le_one, hy]; exact pow_le_one₀ (norm_nonneg _) h1.le
  have hπ0 : (π₀ : F) ≠ 0 := fun h => by rw [h] at h0; simp at h0
  set w : F := y / π₀ ^ i with hw
  have hwn : ‖(w : PadicAlgCl q)‖ = 1 := by
    rw [hw]; push_cast; rw [norm_div, norm_pow, hy, div_self (pow_ne_zero _ h0.ne')]
  have hwR : w ∈ Rw q F := (mem_Rw_iff_norm_le_one q F _).mpr hwn.le
  obtain ⟨wu, hwu⟩ := isUnit_of_norm_coe_eq_one q F (x := ⟨w, hwR⟩) hwn
  refine ⟨hπR, hyR, wu, Subtype.ext ?_⟩
  have : ((wu : Rw q F) : F) = w := congrArg Subtype.val hwu
  push_cast
  rw [this, hw, mul_div_cancel₀ _ (pow_ne_zero _ hπ0)]

set_option maxHeartbeats 6400000 in

theorem maximalIdeal_eq_span [IsDiscreteValuationRing (Rw q F)] {π₀ : F} (h0 : 0 < ‖(π₀ : PadicAlgCl q)‖)
    (h1 : ‖(π₀ : PadicAlgCl q)‖ < 1) (hall : ∀ y : F, y ≠ 0 → ∃ i : ℤ, ‖(y : PadicAlgCl q)‖ = ‖(π₀ : PadicAlgCl q)‖ ^ i)
    (hπ : π₀ ∈ Rw q F) :
    IsLocalRing.maximalIdeal (Rw q F) = Ideal.span {(⟨π₀, hπ⟩ : Rw q F)} := by
  apply le_antisymm
  · intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact Ideal.zero_mem _
    have hx0' : (x : F) ≠ 0 := fun h => hx0 (Subtype.ext h)
    obtain ⟨i, hi⟩ := hall (x : F) hx0'

    have hxlt : ‖((x : F) : PadicAlgCl q)‖ < 1 := by
      have hle : ‖((x : F) : PadicAlgCl q)‖ ≤ 1 := (mem_Rw_iff_norm_le_one q F _).mp x.2
      rcases hle.lt_or_eq with h | h
      · exact h
      · exact absurd (isUnit_of_norm_coe_eq_one q F h) ((IsLocalRing.mem_maximalIdeal _).mp hx)
    have hipos : 0 < i := by
      rw [hi] at hxlt
      exact (zpow_lt_one_iff_right_of_lt_one₀ h0 h1).mp hxlt
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hipos.le
    rw [hk, zpow_natCast] at hi
    obtain ⟨hπ', hy', w, hw⟩ := exists_unit_eq_pow_mul q F h0 h1 hi
    have hk1 : 1 ≤ k := by omega
    have : x = ⟨π₀, hπ⟩ ^ k * (w : Rw q F) := by
      have hxx : x = ⟨(x : F), hy'⟩ := Subtype.ext rfl
      rw [hxx, hw]
    rw [this]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) k hk1)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := norm_coe_unit_eq_one q F hu
    exact h1.ne this

end Ws26L3

set_option maxHeartbeats 160000000 in
open Ws26T4D ExtCitation.LocalLevel IsLocalRing groupCohomology IntermediateField in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (E : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K E]
    (N : ℕ) (hN : 0 < N)
    [FiniteDimensional K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})] [Normal K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})]
    [FiniteDimensional E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})] [Normal E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})]
    (φK : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (hφK : ∀ σ, σ ∈ Subgroup.zpowers φK)
    (j : ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) →* ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})))
    (hj : ∀ (σ : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (x : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (y : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})),
      (x : PadicAlgCl q) = (y : PadicAlgCl q) → ((j σ x : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) = ((σ y : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q))
    (ψ : Rep.res j (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) ⟶ Rep.ofAlgebraAutOnUnits E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))
    (hψ : ∀ u : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ,
      (((Additive.toMul (ψ.hom (Additive.ofMul u)) : ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ) : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q)
        = ((u : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q))
    (π : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ) (hπK : ((π : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) ∈ (K : Set (PadicAlgCl q)))
    (hcoc : carryFun φK hφK (isOfFinOrder_of_finite φK) (A := Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (Additive.ofMul π)
      ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})))
    (hdvd : Module.finrank K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ∣ Module.finrank K E) :
    (groupCohomology.map j ψ 2).hom
        ((H2π (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))).hom
          ⟨carryFun φK hφK (isOfFinOrder_of_finite φK) (A := Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (Additive.ofMul π), hcoc⟩) = 0 := by
  classical

  set E' : IntermediateField ℚ_[q] (PadicAlgCl q) := E.restrictScalars ℚ_[q] with hE'
  haveI : FiniteDimensional ℚ_[q] E := Module.Finite.trans K E
  haveI : FiniteDimensional ℚ_[q] E' := (inferInstance : FiniteDimensional ℚ_[q] E)
  haveI : FiniteDimensional (↥E') (IntermediateField.adjoin (↥E') {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) :=
    (inferInstance : FiniteDimensional E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))
  haveI : Normal (↥E') (IntermediateField.adjoin (↥E') {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) :=
    (inferInstance : Normal E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))
  obtain ⟨φE, hφE, -⟩ :
      ∃ φ : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}), (∀ σ, σ ∈ Subgroup.zpowers φ) ∧
        ∃ a : ℕ, 0 < a ∧ ∀ ζ : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}), (ζ : PadicAlgCl q) ^ (q ^ N - 1) = 1 → (φ ζ : PadicAlgCl q) = (ζ : PadicAlgCl q) ^ (q ^ a) :=
    IntermediateField.exists_generator_frobenius_adjoin_rootsOfUnity_padic q E' N hN
  have hfinK : IsOfFinOrder φK := isOfFinOrder_of_finite φK
  have hfinE : IsOfFinOrder φE := isOfFinOrder_of_finite φE

  have hle : IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} ≤ (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}).restrictScalars K := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    exact IntermediateField.subset_adjoin E _ hz

  have hjinj : Function.Injective j := by
    intro σ τ hστ
    have key : ∀ ρ : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}), j ρ = 1 → ρ = 1 := by
      intro ρ hρ
      apply AlgEquiv.ext
      intro y
      apply Subtype.ext

      refine IntermediateField.adjoin_induction E (s := {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})
        (p := fun z hz => ((ρ ⟨z, hz⟩ : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) = z) ?_ ?_ ?_ ?_ ?_ y.2
      · intro z hz
        have hzK : z ∈ IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} :=
          IntermediateField.subset_adjoin K _ hz
        have := hj ρ ⟨z, hzK⟩ ⟨z, hle hzK⟩ rfl
        rw [hρ] at this
        exact this.symm
      · intro x
        show ((ρ (algebraMap E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) x) : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) = _
        rw [AlgEquiv.commutes]; rfl
      · intro x z hx hz hpx hpz
        have : (⟨x + z, add_mem hx hz⟩ : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) = ⟨x, hx⟩ + ⟨z, hz⟩ := rfl
        rw [this, map_add]
        push_cast
        rw [hpx, hpz]
      · intro x hx hpx
        have : (⟨x⁻¹, inv_mem hx⟩ : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) = (⟨x, hx⟩ : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))⁻¹ := rfl
        rw [this, map_inv₀]
        push_cast
        rw [hpx]
      · intro x z hx hz hpx hpz
        have : (⟨x * z, mul_mem hx hz⟩ : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) = ⟨x, hx⟩ * ⟨z, hz⟩ := rfl
        rw [this, map_mul]
        push_cast
        rw [hpx, hpz]
    have h1 : j (σ * τ⁻¹) = 1 := by rw [map_mul, map_inv, hστ, mul_inv_cancel]
    have := key _ h1
    rwa [mul_inv_eq_one] at this

  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : ℕ, j φE = φK ^ f₀ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hφK (j φE))
    refine ⟨(k % orderOf φK).toNat, ?_⟩
    have hnn : 0 ≤ k % orderOf φK := Int.emod_nonneg _ (by exact_mod_cast (orderOf_pos_iff.mpr hfinK).ne')
    rw [← hk, ← zpow_natCast, Int.toNat_of_nonneg hnn, zpow_mod_orderOf]

  set πK : K := ⟨(π : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})), hπK⟩ with hπKdef
  have hπalg : (π : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) = algebraMap K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) πK := Subtype.ext rfl
  have haK : (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})).ρ φK (Additive.ofMul π) = Additive.ofMul π := by
    show (Rep.ofMulDistribMulAction ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ).ρ φK (Additive.ofMul π) = Additive.ofMul π
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
    congr 1
    apply Units.ext
    show φK (π : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) = π
    rw [hπalg, AlgEquiv.commutes]

  have hπE : ((π : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) ∈ E := by
    have := IntermediateField.algebraMap_mem E πK
    exact this
  set πE : E := ⟨((π : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q), hπE⟩ with hπEdef
  set uE : ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ := Additive.toMul (ψ.hom (Additive.ofMul π)) with huE
  have huEval : (uE : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) = algebraMap E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) πE := by
    apply Subtype.ext
    show ((uE : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) = (πE : PadicAlgCl q)
    rw [huE, hψ]
  have hψπ : ψ.hom (Additive.ofMul π) = Additive.ofMul uE := by rw [huE, ofMul_toMul]
  have haE : (Rep.ofAlgebraAutOnUnits E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})).ρ φE (ψ.hom (Additive.ofMul π)) = ψ.hom (Additive.ofMul π) := by
    rw [hψπ]
    show (Rep.ofMulDistribMulAction ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ).ρ φE (Additive.ofMul uE) = Additive.ofMul uE
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
    congr 1
    apply Units.ext
    show φE (uE : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) = uE
    rw [huEval, AlgEquiv.commutes]
  have hzb := groupCohomology.carryFun_mem_cocycles2 φE hφE hfinE _ haE

  rw [groupCohomology.map_carry_H2pi_eq_smul_carry j hjinj φK hφK (isOfFinOrder_of_finite φK) f₀ φE hf₀ hφE hfinE
    _ _ ψ (Additive.ofMul π) haK hcoc hzb]

  suffices h0 : (H2π (Rep.ofAlgebraAutOnUnits E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))).hom ⟨carryFun φE hφE hfinE (ψ.hom (Additive.ofMul π)), hzb⟩ = 0 by
    rw [h0, smul_zero]
  rw [groupCohomology.carry_H2pi_eq_zero_iff φE hφE hfinE _ haE hzb]

  haveI : IsGalois E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := ⟨⟩
  have hnE : orderOf φE = Module.finrank E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hφE, IsGalois.card_aut_eq_finrank]

  have hdegK : Module.finrank K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) = orderOf ((Nat.card (ResidueField (Rw q K)) : ZMod (q ^ N - 1))) :=
    IntermediateField.finrank_adjoin_rootsOfUnity_padic_eq_orderOf q K N hN
  have hdegE : Module.finrank E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) = orderOf ((Nat.card (ResidueField (Rw q E')) : ZMod (q ^ N - 1))) :=
    IntermediateField.finrank_adjoin_rootsOfUnity_padic_eq_orderOf q E' N hN
  have hKE' : K ≤ E' := fun x hx => (IntermediateField.algebraMap_mem E ⟨x, hx⟩ : (x : PadicAlgCl q) ∈ E)
  haveI : IsDiscreteValuationRing (Rw q K) := ExtCitation.LocalLevel.isDiscreteValuationRing_Rw q K
  haveI : IsDiscreteValuationRing (Rw q E') := ExtCitation.LocalLevel.isDiscreteValuationRing_Rw q E'
  obtain ⟨e, f, ι, hιval, -, hfpos, hspan, hcardres, hfinrank⟩ :=
    ExtCitation.LocalLevel.exists_relative_ramification_inertia_Rw q K E' hKE'

  have hef : e * f = Module.finrank K E := by
    have htower : Module.finrank ℚ_[q] E' = Module.finrank ℚ_[q] K * Module.finrank K E :=
      (Module.finrank_mul_finrank ℚ_[q] K E).symm
    rw [htower] at hfinrank
    exact (Nat.eq_of_mul_eq_mul_left Module.finrank_pos hfinrank).symm

  set n := Module.finrank K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) with hn
  have hnpos : 0 < n := Module.finrank_pos
  have hn' : Module.finrank E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) = n / Nat.gcd n f := by
    rw [hdegE, hcardres, Nat.cast_pow, orderOf_pow' _ hfpos.ne', ← hdegK]
  have hn'e : Module.finrank E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ∣ e := by
    rw [hn']
    have hg : 0 < Nat.gcd n f := Nat.gcd_pos_of_pos_left f hnpos
    have hn_eq : n / Nat.gcd n f * Nat.gcd n f = n := Nat.div_mul_cancel (Nat.gcd_dvd_left n f)
    have hf_eq : f / Nat.gcd n f * Nat.gcd n f = f := Nat.div_mul_cancel (Nat.gcd_dvd_right n f)
    have h1 : n / Nat.gcd n f ∣ e * (f / Nat.gcd n f) := by
      have h2 : n / Nat.gcd n f * Nat.gcd n f ∣ e * (f / Nat.gcd n f) * Nat.gcd n f := by
        rw [hn_eq, mul_assoc, hf_eq, hef]; exact hdvd
      exact Nat.dvd_of_mul_dvd_mul_right hg h2
    exact (Nat.coprime_div_gcd_div_gcd hg).dvd_of_dvd_mul_right h1

  obtain ⟨πK₀, hK₀pos, hK₀lt, hK₀⟩ := IntermediateField.exists_uniformiser_padic q K
  obtain ⟨πE₀, hE₀pos, hE₀lt, hE₀⟩ := IntermediateField.exists_uniformiser_padic q E'
  have hπK₀E : (πK₀ : PadicAlgCl q) ∈ E' := hKE' πK₀.2
  have hπK₀ne : (⟨(πK₀ : PadicAlgCl q), hπK₀E⟩ : E') ≠ 0 := by
    intro h
    have : (πK₀ : PadicAlgCl q) = 0 := congrArg Subtype.val h
    rw [this, norm_zero] at hK₀pos; exact lt_irrefl _ hK₀pos
  obtain ⟨e', he'⟩ := hE₀ ⟨(πK₀ : PadicAlgCl q), hπK₀E⟩ hπK₀ne
  change ‖(πK₀ : PadicAlgCl q)‖ = ‖(πE₀ : PadicAlgCl q)‖ ^ e' at he'
  have he'pos : 0 < e' := by
    rw [he'] at hK₀lt
    exact (zpow_lt_one_iff_right_of_lt_one₀ hE₀pos hE₀lt).mp hK₀lt
  obtain ⟨e'', he''⟩ := Int.eq_ofNat_of_zero_le he'pos.le
  rw [he'', zpow_natCast] at he'

  have hπK₀R : πK₀ ∈ Rw q K := (mem_Rw_iff_norm_le_one q K _).mpr hK₀lt.le
  have hπE₀R : πE₀ ∈ Rw q E' := (mem_Rw_iff_norm_le_one q E' _).mpr hE₀lt.le
  have hmK : maximalIdeal (Rw q K) = Ideal.span {(⟨πK₀, hπK₀R⟩ : Rw q K)} :=
    Ws26L3.maximalIdeal_eq_span q K hK₀pos hK₀lt hK₀ hπK₀R
  have hmE : maximalIdeal (Rw q E') = Ideal.span {(⟨πE₀, hπE₀R⟩ : Rw q E')} :=
    Ws26L3.maximalIdeal_eq_span q E' hE₀pos hE₀lt hE₀ hπE₀R
  have he2 : ‖(((⟨(πK₀ : PadicAlgCl q), hπK₀E⟩ : E') : PadicAlgCl q))‖ = ‖(πE₀ : PadicAlgCl q)‖ ^ e'' := he'
  obtain ⟨hπE₀R', hyR, w₀, hw₀⟩ := Ws26L3.exists_unit_eq_pow_mul q E' hE₀pos hE₀lt he2
  have hιπ : ι ⟨πK₀, hπK₀R⟩ = ⟨⟨(πK₀ : PadicAlgCl q), hπK₀E⟩, hyR⟩ := by
    apply Subtype.ext; apply Subtype.ext
    exact hιval ⟨πK₀, hπK₀R⟩
  have hee : e'' = e := by
    have h1 : Ideal.map ι (maximalIdeal (Rw q K)) = maximalIdeal (Rw q E') ^ e'' := by
      rw [hmK, Ideal.map_span, Set.image_singleton, hιπ, hw₀, hmE, Ideal.span_singleton_pow,
        Ideal.span_singleton_mul_right_unit w₀.isUnit]
    rw [hspan] at h1
    have hne : maximalIdeal (Rw q E') ≠ ⊥ := IsDiscreteValuationRing.not_a_field (Rw q E')
    have hne' : maximalIdeal (Rw q E') ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
    exact ((Ideal.pow_right_strictAnti _ hne hne').injective h1).symm

  have hπne : (πK : K) ≠ 0 := by
    intro h
    have : (π : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) = 0 := by rw [hπalg, h, map_zero]
    exact π.ne_zero this
  obtain ⟨k, hk⟩ := hK₀ πK hπne
  change ‖((π : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q)‖ = ‖(πK₀ : PadicAlgCl q)‖ ^ k at hk
  rw [he', ← zpow_natCast, ← zpow_mul] at hk

  obtain ⟨M, hM⟩ : ((Module.finrank E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) : ℕ) : ℤ) ∣ (e'' : ℤ) * k :=
    Dvd.dvd.mul_right (by rw [hee]; exact_mod_cast hn'e) k

  have hπE₀ne : (πE₀ : E') ≠ 0 := fun h => by rw [h] at hE₀pos; simp at hE₀pos
  set πE' : E' := ⟨((π : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q), hπE⟩ with hπE'def
  set w : E' := πE' / (πE₀ : E') ^ ((e'' : ℤ) * k) with hwdef
  have hwnorm : ‖(w : PadicAlgCl q)‖ = 1 := by
    have hcoe : ((w : E') : PadicAlgCl q) = (πE' : PadicAlgCl q) / (πE₀ : PadicAlgCl q) ^ ((e'' : ℤ) * k) := by
      rw [hwdef]
      change algebraMap (↥E') (PadicAlgCl q) (πE' / πE₀ ^ ((e'' : ℤ) * k)) = _
      rw [map_div₀, map_zpow₀]; rfl
    rw [hcoe, norm_div, norm_zpow, ← hk]
    exact div_self (by rw [norm_ne_zero_iff]; exact fun h => hπne (Subtype.ext h))
  obtain ⟨b, hb⟩ := IntermediateField.exists_norm_eq_of_nnnorm_eq_one_adjoin_rootsOfUnity_padic q E' N hN w hwnorm

  haveI : IsGalois (↥E') (IntermediateField.adjoin (↥E') {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := ⟨⟩
  have hπE0 : πE' ≠ 0 := by
    intro h
    have : ((π : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) = 0 := congrArg Subtype.val h
    exact hπne (Subtype.ext this)
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, Algebra.norm_zero] at hb
    have : (w : E') = 0 := hb.symm
    rw [this, ZeroMemClass.coe_zero, norm_zero] at hwnorm
    exact zero_ne_one hwnorm
  set N' : ((IntermediateField.adjoin (↥E') {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ →* (↥E')ˣ := Units.map (Algebra.norm (↥E') : (IntermediateField.adjoin (↥E') {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) →* ↥E') with hN'
  have hN'val : ∀ u : ((IntermediateField.adjoin (↥E') {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ, ((N' u : (↥E')ˣ) : E') = Algebra.norm (↥E') (u : (IntermediateField.adjoin (↥E') {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) := fun _ => rfl

  have hπE₀u : (Units.mk0 (πE₀ : E') hπE₀ne) ^ (Module.finrank E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) ∈ N'.range := by
    refine ⟨Units.mk0 (algebraMap (↥E') (IntermediateField.adjoin (↥E') {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) πE₀) (by rw [Ne, map_eq_zero_iff _ (algebraMap (↥E') (IntermediateField.adjoin (↥E') {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})).injective]; exact hπE₀ne), ?_⟩
    apply Units.ext
    rw [hN'val, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0, Algebra.norm_algebraMap]
    rfl
  have hwu : Units.mk0 w (by
      intro h; rw [h, ZeroMemClass.coe_zero, norm_zero] at hwnorm; exact zero_ne_one hwnorm) ∈ N'.range := by
    refine ⟨Units.mk0 b hb0, Units.ext ?_⟩
    rw [hN'val, Units.val_mk0, Units.val_mk0, hb]
  have hπu : Units.mk0 πE' hπE0 ∈ N'.range := by
    have hdecomp : Units.mk0 πE' hπE0
        = ((Units.mk0 (πE₀ : E') hπE₀ne) ^ (Module.finrank E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))) ^ M * Units.mk0 w (by
            intro h; rw [h, ZeroMemClass.coe_zero, norm_zero] at hwnorm; exact zero_ne_one hwnorm) := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_mk0]
      rw [hwdef, ← zpow_natCast, ← zpow_mul, ← hM, mul_div_cancel₀ _ (zpow_ne_zero _ hπE₀ne)]
    rw [hdecomp]
    exact N'.range.mul_mem (N'.range.zpow_mem hπE₀u M) hwu
  obtain ⟨cu, hcu⟩ := hπu

  set cE : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := ((cu : (IntermediateField.adjoin (↥E') {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) with hcEdef
  have hcE0 : cE ≠ 0 := cu.ne_zero
  have hnormc : Algebra.norm E cE = πE := by
    have h1 : Algebra.norm (↥E') (cu : (IntermediateField.adjoin (↥E') {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) = πE' := by
      have := congrArg (fun u : (↥E')ˣ => (u : E')) hcu
      simpa only [hN'val, Units.val_mk0] using this
    exact h1

  have hprod : (∏ i ∈ Finset.range (orderOf φE), (φE ^ i) cE) = algebraMap E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) πE := by
    rw [← hnormc, Algebra.norm_eq_prod_automorphisms]
    have hinj : Function.Injective (fun i : Fin (orderOf φE) => φE ^ (i : ℕ)) := by
      intro i i' h
      exact Fin.ext (pow_injOn_Iio_orderOf i.isLt i'.isLt h)
    have hsurj : Function.Surjective (fun i : Fin (orderOf φE) => φE ^ (i : ℕ)) := by
      intro σ
      have hmem : σ ∈ Submonoid.powers φE := by
        rw [mem_powers_iff_mem_zpowers]; exact hφE σ
      rw [mem_powers_iff_mem_range_orderOf] at hmem
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmem
      exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
    let eqv : Fin (orderOf φE) ≃ ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) := Equiv.ofBijective _ ⟨hinj, hsurj⟩
    rw [← Fin.prod_univ_eq_prod_range (fun i => (φE ^ i) cE) (orderOf φE)]
    exact Fintype.prod_equiv eqv (fun i => (φE ^ (i : ℕ)) cE) (fun σ => σ cE) (fun _ => rfl)
  refine ⟨Additive.ofMul (Units.mk0 cE hcE0), ?_⟩
  rw [hψπ]
  have h2 : ∀ i, (Rep.ofAlgebraAutOnUnits E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})).ρ (φE ^ i) (Additive.ofMul (Units.mk0 cE hcE0))
      = Additive.ofMul ((φE ^ i) • Units.mk0 cE hcE0) := fun i => rfl
  have h3 : Additive.ofMul (∏ i ∈ Finset.range (orderOf φE), (φE ^ i) • Units.mk0 cE hcE0)
      = ∑ i ∈ Finset.range (orderOf φE), (Rep.ofAlgebraAutOnUnits E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})).ρ (φE ^ i) (Additive.ofMul (Units.mk0 cE hcE0)) := by
    rw [ofMul_prod]
    simp only [← h2]
    rfl
  have h4 : Additive.ofMul (∏ i ∈ Finset.range (orderOf φE), (φE ^ i) • Units.mk0 cE hcE0) = Additive.ofMul uE := by
    congr 1
    apply Units.ext
    rw [Units.coe_prod, huEval, ← hprod]
    exact Finset.prod_congr rfl fun i _ => rfl
  exact h3.symm.trans h4

end S_groupCohomology_map_carryFun_adjoin_rootsOfUnity_eq_zero_of_dvd
end P2MW
export P2MW.S_groupCohomology_map_carryFun_adjoin_rootsOfUnity_eq_zero_of_dvd (solution)
