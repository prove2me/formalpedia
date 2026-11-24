-- Prove2me | Theorems.Thm_CyclotomicIntegers_one_sub_zeta_dvd_int_iff
-- name    : CyclotomicIntegers.one_sub_zeta_dvd_int_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:43.962358+00:00
-- url     : https://prove2.me/theorems/29a14466-c2f6-4d18-a372-4682dcfb9675
-- title:
--   Cyclotomic Integers: one sub zeta dvd int iff
-- statement:
--   The Cyclotomic Integers construction uses the one sub zeta dvd int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L78-L82

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_Rat
public import Definitions.Def_FltRegular_NumberTheory_CyclotomicRing
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open Polynomial NumberField
variable (p : ℕ) [hpri : Fact p.Prime]
open CyclotomicIntegers

theorem CyclotomicIntegers.one_sub_zeta_dvd_int_iff (n : ℤ) : 1 - zeta p ∣ n ↔ ↑p ∣ n := by sorry
