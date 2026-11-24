-- Prove2me | solution 1 for isRegularPrime_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:28.173989+00:00
-- url     : https://prove2.me/submissions/ca8d8eb2-068c-4ee6-9708-3ca9ff16e019

module
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_Rat
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Theorems.Thm_isRegularPrime_of_isPrincipalIdealRing

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open Nat Polynomial NumberField
open scoped NumberField
variable (n p : ℕ)
variable (K : Type*) [Field K]
variable (L : Type*) [Field L] [Algebra K L]
theorem _root_.solution : IsRegularPrime 3 :=
  have := IsCyclotomicExtension.Rat.three_pid (CyclotomicField 3 ℚ)
  isRegularPrime_of_isPrincipalIdealRing 3
