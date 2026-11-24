-- Prove2me | solution 1 for isRegularPrime_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:03.541733+00:00
-- url     : https://prove2.me/submissions/3707acdc-30e5-4a78-bfa3-1dcc0d6e92b9

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
theorem _root_.solution : IsRegularPrime 2 := isRegularPrime_of_isPrincipalIdealRing 2
