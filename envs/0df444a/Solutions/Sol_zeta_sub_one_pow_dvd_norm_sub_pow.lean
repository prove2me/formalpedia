-- Prove2me | solution 1 for zeta_sub_one_pow_dvd_norm_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:51.291384+00:00
-- url     : https://prove2.me/submissions/be18c7b8-ccb7-4a2c-8552-204f66d7494b

module
public import Mathlib.RingTheory.NormTrace
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Theorems.Thm_zeta_sub_one_dvd_trace_sub_smul

set_option autoImplicit false
@[expose] public section
public section
variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K]
  [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
open scoped nonZeroDivisors NumberField
open Polynomial IsCyclotomicExtension.Rat
variable (hp : p ≠ 2)
theorem _root_.solution (x : 𝓞 K) :
    (hζ.toInteger - 1 : 𝓞 K) ^ p ∣
      (Algebra.norm ℤ (1 + p • x) : 𝓞 K) - 1 + p • x := by
  let _ := IsCyclotomicExtension.numberField {p} ℚ K
  obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul (p : ℤ) x
  obtain ⟨s, hs⟩ := zeta_sub_one_dvd_trace_sub_smul hζ x
  obtain ⟨t, ht⟩ := (associated_zeta_sub_one_pow_prime _ hζ).dvd
  rw [sub_eq_iff_eq_add] at hs
  simp only [zsmul_eq_mul, Int.cast_natCast] at hr
  simp only [nsmul_eq_mul, hr, Int.cast_add, Int.cast_one, Int.cast_mul, hs, NeZero.pos p,
    Nat.cast_pred, Int.cast_natCast, Int.cast_pow]
  suffices (hζ.toInteger - 1 : 𝓞 K) ^ p ∣
      (hζ.toInteger - 1) * p * s + (p : 𝓞 K) ^ 2 * (r + x) by
    convert this using 1
    ring
  apply dvd_add
  · apply dvd_mul_of_dvd_left
    rw [ht, ← mul_assoc, ← pow_succ', tsub_add_cancel_of_le (Nat.Prime.one_lt hpri.out).le]
    exact dvd_mul_right _ _
  · rw [ht, mul_pow, ← pow_mul, mul_assoc]
    apply dvd_mul_of_dvd_left
    apply pow_dvd_pow
    zify [(Nat.Prime.one_lt hpri.out).le]
    linarith only [Nat.Prime.two_le hpri.out]
