-- Prove2me | Theorems.Thm_CyclotomicIntegers_not_isUnit_one_sub_zeta
-- name    : CyclotomicIntegers.not_isUnit_one_sub_zeta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:52.515198+00:00
-- url     : https://prove2.me/theorems/8facde6c-88ad-4bc0-9478-9cb84b6da5b2
-- title:
--   Cyclotomic Integers: not is Unit one sub zeta
-- statement:
--   The Cyclotomic Integers construction uses the not is Unit one sub zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L75-L76

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

theorem CyclotomicIntegers.not_isUnit_one_sub_zeta :
    ¬ IsUnit (1 - zeta p) := by sorry
