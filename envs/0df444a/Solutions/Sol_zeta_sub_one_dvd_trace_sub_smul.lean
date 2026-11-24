-- Prove2me | solution 1 for zeta_sub_one_dvd_trace_sub_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:05.677533+00:00
-- url     : https://prove2.me/submissions/06da4cfe-2d84-4ef0-b659-a88a24a45b80

module
public import Mathlib.RingTheory.NormTrace
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Theorems.Thm_quotient_zero_sub_one_comp_aut

set_option autoImplicit false
@[expose] public section
public section
variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K]
  [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
open scoped nonZeroDivisors NumberField
open Polynomial IsCyclotomicExtension.Rat
variable (hp : p ≠ 2)
open NumberField.RingOfIntegers
theorem _root_.solution (x : 𝓞 K) :
    (hζ.toInteger - 1 : 𝓞 K) ∣ Algebra.trace ℤ _ x - (p - 1) • x := by
  let _ := IsCyclotomicExtension.numberField {p} ℚ K
  let _ := IsCyclotomicExtension.isGalois {p} ℚ K
  have htrace : (Algebra.trace ℤ _ x : 𝓞 K) =
      ∑ σ : K ≃ₐ[ℚ] K, (mapAlgHom σ).toRingHom x := by
    apply (show Function.Injective (algebraMap (𝓞 K) K) from Subtype.val_injective)
    rw [← eq_intCast (algebraMap ℤ (𝓞 K)), ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply ℤ ℚ K, eq_intCast, Algebra.coe_trace_int,
      trace_eq_sum_automorphisms, map_sum]
    rfl
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, htrace,
    map_sum]
  simp_rw [← RingHom.comp_apply, quotient_zero_sub_one_comp_aut]
  rw [Finset.sum_const, map_nsmul, sub_eq_zero, Finset.card_univ, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank,
    IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat (NeZero.pos p)),
    Nat.totient_prime hpri.out]
