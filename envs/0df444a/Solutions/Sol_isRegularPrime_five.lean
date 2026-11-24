-- Prove2me | solution 1 for isRegularPrime_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:07.241498+00:00
-- url     : https://prove2.me/submissions/b0a22fc1-ea04-4705-9d4d-cc1a5b5597b1

module
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import Definitions.Def_FltRegular_FltRegular
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_SmallNumbers_Five_FLT5
public import Theorems.Thm_isRegularPrime_of_isPrincipalIdealRing


set_option autoImplicit false
@[expose] public section
public section
open Nat NumberField IsCyclotomicExtension
theorem _root_.solution : IsRegularPrime 5 :=
  have := Rat.five_pid (CyclotomicField 5 ℚ)
  isRegularPrime_of_isPrincipalIdealRing 5
