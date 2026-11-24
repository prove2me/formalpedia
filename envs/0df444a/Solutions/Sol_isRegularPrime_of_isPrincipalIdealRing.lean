-- Prove2me | solution 1 for isRegularPrime_of_isPrincipalIdealRing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:32:49.415043+00:00
-- url     : https://prove2.me/submissions/a2388c88-2e63-41aa-8f15-af1e73acb7a8

module
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_Rat
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open Nat Polynomial NumberField
open scoped NumberField
variable (n p : ℕ)
theorem _root_.solution [IsPrincipalIdealRing (𝓞 (CyclotomicField p ℚ))] :
    IsRegularPrime p := by
  rw [IsRegularPrime, IsRegularNumber, card_classGroup_eq_one_iff.2 ‹_›]
  exact coprime_one_right _
