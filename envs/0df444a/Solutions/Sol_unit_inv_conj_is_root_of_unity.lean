-- Prove2me | solution 1 for unit_inv_conj_is_root_of_unity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:56.674013+00:00
-- url     : https://prove2.me/submissions/db832057-2ee9-4ac0-84fd-dee03b429b93

module
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_UnitLemmas
public import Theorems.Thm_unit_inv_conj_not_neg_zeta_runity

set_option autoImplicit false
@[expose] public section
public section
variable {p : ℕ} [NeZero p] {K : Type*} [Field K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
open scoped nonZeroDivisors NumberField
open IsCyclotomicExtension NumberField Polynomial IsCMField
noncomputable section
local notation3 "η" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit
set_option quotPrecheck false
local notation "I" => (Ideal.span ({(η - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K))
variable [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem _root_.solution (u : (𝓞 K)ˣ) [H : Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    ∃ m : ℕ, u * (unitsComplexConj K u)⁻¹ = (η ^ m) ^ 2 := by
  let _ := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  have hpo : Odd p := H.out.odd_of_ne_two hp.ne'
  have hη : (η : K) = ζ := by rw [IsUnit.unit_spec]; rfl
  have hroot : IsOfFinOrder (u * (unitsComplexConj K u)⁻¹ : K) := by
    have h : IsOfFinOrder (u * (unitsComplexConj K u)⁻¹) :=
      (CommGroup.mem_torsion _).mp (unitsMulComplexConjInv K u).property
    exact (Function.Injective.isOfFinOrder_iff
      (f := (algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K)))
      (NumberField.Units.coe_injective K)).mpr h
  obtain ⟨n, -, hz | hz⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder hpo hroot
  · have hz' : u * (unitsComplexConj K u)⁻¹ = η ^ n := by
      apply NumberField.Units.coe_injective
      simpa only [NumberField.Units.coe_mul, NumberField.Units.coe_pow, hη] using hz
    rw [hz']
    simpa only [pow_mul, mul_comm] using
      ((hζ.toInteger_isPrimitiveRoot.isUnit_unit (NeZero.ne p)).exists_pow_eq_pow_two_mul hpo n)
  · exfalso
    apply unit_inv_conj_not_neg_zeta_runity hζ u n hp
    apply NumberField.Units.coe_injective
    simpa only [NumberField.Units.coe_mul, NumberField.Units.coe_pow,
      Units.val_neg, map_neg, hη] using hz
