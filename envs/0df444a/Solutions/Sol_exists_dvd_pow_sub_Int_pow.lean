-- Prove2me | solution 1 for exists_dvd_pow_sub_Int_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:49.626323+00:00
-- url     : https://prove2.me/submissions/9a0d85be-7c6c-43c5-b1cd-b47bbe343b5b

module
public import Mathlib.RingTheory.NormTrace
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Theorems.Thm_exists_zeta_sub_one_dvd_sub_Int

set_option autoImplicit false
@[expose] public section
public section
variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K]
  [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
open scoped nonZeroDivisors NumberField
open Polynomial IsCyclotomicExtension.Rat
variable (hp : p ≠ 2)
include hp
theorem _root_.solution (a : 𝓞 K) : ∃ b : ℤ, ↑p ∣ a ^ p - (b : 𝓞 K) ^ p := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ K (Set.mem_singleton p)
    hpri.1.ne_zero
  obtain ⟨b, k, e⟩ := exists_zeta_sub_one_dvd_sub_Int hζ a
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hpri.out a (-b)
  obtain ⟨u, hu⟩ := (associated_zeta_sub_one_pow_prime _ hζ).symm
  rw [(Nat.Prime.odd_of_ne_two hpri.out hp).neg_pow, ← sub_eq_add_neg, e,
    mul_pow, ← sub_eq_add_neg] at hr
  use b, ↑u * ((hζ.toInteger - 1 : 𝓞 K) * k ^ p) - r * a * (-b)
  rw [← sub_eq_iff_eq_add.mpr hr, mul_sub, ← mul_assoc, ← mul_assoc, hu, ← pow_succ,
    Nat.sub_add_cancel (n := p) (m := 1) hpri.out.one_lt.le]
  ring
