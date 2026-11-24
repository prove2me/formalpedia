-- Prove2me | Theorems.Thm_CyclotomicIntegers_isCoprime_one_sub_zeta
-- name    : CyclotomicIntegers.isCoprime_one_sub_zeta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:45.1838+00:00
-- url     : https://prove2.me/theorems/4659a47f-8afe-461d-8169-f1912140caf5
-- title:
--   Cyclotomic Integers: is Coprime one sub zeta
-- statement:
--   The Cyclotomic Integers construction uses the is Coprime one sub zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L87-L89

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

theorem CyclotomicIntegers.isCoprime_one_sub_zeta (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) : IsCoprime (1 - zeta p) n := by sorry
