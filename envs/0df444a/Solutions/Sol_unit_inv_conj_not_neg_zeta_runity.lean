-- Prove2me | solution 1 for unit_inv_conj_not_neg_zeta_runity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:59.697973+00:00
-- url     : https://prove2.me/submissions/95776840-e954-43ad-bdb4-7ac2a33efa51

module
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_UnitLemmas
public import Theorems.Thm_eq_one_mod_one_sub
public import Theorems.Thm_unit_inv_conj_not_neg_zeta_runity_aux

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
theorem _root_.solution (u : (𝓞 K)ˣ) (n : ℕ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    u * (unitsComplexConj K u)⁻¹ ≠ -η ^ n := by
  by_contra H
  have hμ : algebraMap (𝓞 K) (𝓞 K ⧸ I) ((η : 𝓞 K) ^ n) = 1 := by
    rw [map_pow, eq_one_mod_one_sub, one_pow]
  have hμ' : algebraMap (𝓞 K) (𝓞 K ⧸ I) ((η : 𝓞 K) ^ n) = -1 := by
    rw [← neg_eq_iff_eq_neg, ← map_neg, ← Units.val_pow_eq_pow_val, ← Units.val_neg, ← H]
    apply unit_inv_conj_not_neg_zeta_runity_aux hζ u hp
  let _ := Fact.mk hp
  apply (IsCyclotomicExtension.Rat.two_not_mem_span_zeta_sub_one' _ hζ hp : (2 : 𝓞 K) ∉ I)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat, ← one_add_one_eq_two,
    ← neg_eq_iff_add_eq_zero]
  exact hμ'.symm.trans hμ
