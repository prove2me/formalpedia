-- Prove2me | Theorems.Thm_CyclotomicIntegers_prime_one_sub_zeta
-- name    : CyclotomicIntegers.prime_one_sub_zeta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:50.384102+00:00
-- url     : https://prove2.me/theorems/53a0da3b-a0da-4977-a5cd-3a7a0de775bc
-- title:
--   Cyclotomic Integers: prime one sub zeta
-- statement:
--   The Cyclotomic Integers construction uses the prime one sub zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L64-L69

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

theorem CyclotomicIntegers.prime_one_sub_zeta :
    Prime (1 - zeta p) := by sorry
