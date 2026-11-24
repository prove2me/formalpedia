-- Prove2me | solution 1 for exists_zeta_sub_one_dvd_sub_Int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:03.480317+00:00
-- url     : https://prove2.me/submissions/7be7f501-236d-4df1-8aeb-f1dada400018

module
public import Mathlib.RingTheory.NormTrace
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas

set_option autoImplicit false
@[expose] public section
public section
variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K]
  [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
open scoped nonZeroDivisors NumberField
open Polynomial IsCyclotomicExtension.Rat
variable (hp : p ≠ 2)
theorem _root_.solution (a : 𝓞 K) :
    ∃ b : ℤ, (hζ.toInteger - 1 : 𝓞 K) ∣ a - b := by
  have hdiv := hζ.subOneIntegralPowerBasis.exists_gen_dvd_sub a
  rwa [hζ.subOneIntegralPowerBasis_gen] at hdiv
