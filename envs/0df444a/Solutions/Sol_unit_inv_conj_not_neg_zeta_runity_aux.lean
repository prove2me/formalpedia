-- Prove2me | solution 1 for unit_inv_conj_not_neg_zeta_runity_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:12.823571+00:00
-- url     : https://prove2.me/submissions/3a84b992-eb38-47ab-bfc6-788e5111bf60

module
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_UnitLemmas
public import Theorems.Thm_quotient_zero_sub_one_comp_aut


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
theorem _root_.solution (u : (𝓞 K)ˣ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    algebraMap (𝓞 K) (𝓞 K ⧸ I) (unitsMulComplexConjInv K u).1 = 1 := by
  let _ := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  rw [unitsMulComplexConjInv_apply, Units.val_mul, map_mul]
  have heq : algebraMap (𝓞 K) (𝓞 K ⧸ I) (u : 𝓞 K) =
      algebraMap (𝓞 K) (𝓞 K ⧸ I) ((unitsComplexConj K u : (𝓞 K)ˣ) : 𝓞 K) :=
    (RingHom.congr_fun (quotient_zero_sub_one_comp_aut hζ
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom) (u : 𝓞 K)).symm
  rw [heq, ← map_mul, Units.mul_inv, map_one]
