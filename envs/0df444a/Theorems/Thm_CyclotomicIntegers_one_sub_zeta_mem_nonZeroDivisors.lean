-- Prove2me | Theorems.Thm_CyclotomicIntegers_one_sub_zeta_mem_nonZeroDivisors
-- name    : CyclotomicIntegers.one_sub_zeta_mem_nonZeroDivisors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:47.866376+00:00
-- url     : https://prove2.me/theorems/683c9b03-6652-4106-b2e9-5caeb787349d
-- title:
--   Cyclotomic Integers: one sub zeta mem non Zero Divisors
-- statement:
--   The Cyclotomic Integers construction uses the one sub zeta mem non Zero Divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L71-L73

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

theorem CyclotomicIntegers.one_sub_zeta_mem_nonZeroDivisors :
    1 - zeta p ∈ nonZeroDivisors (CyclotomicIntegers p) := by sorry
