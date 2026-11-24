-- Prove2me | solution 1 for isRegularPrime_seven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:07.761477+00:00
-- url     : https://prove2.me/submissions/9b9d4875-d374-4e36-9ef7-1458718b9ded

module
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_FltRegular_FltRegular
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_SmallNumbers_Seven_Seven
public import Definitions.Def_FltRegular_SmallNumbers_Seven_FLT7
public import Theorems.Thm_Rat_seven_pid
public import Theorems.Thm_isRegularPrime_of_isPrincipalIdealRing


set_option autoImplicit false
@[expose] public section
public section
open Nat NumberField IsCyclotomicExtension
theorem _root_.solution : IsRegularPrime 7 :=
  have := Rat.seven_pid (CyclotomicField 7 ℚ)
  isRegularPrime_of_isPrincipalIdealRing 7
