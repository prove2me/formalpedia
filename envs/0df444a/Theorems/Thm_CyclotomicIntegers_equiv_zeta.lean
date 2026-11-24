-- Prove2me | Theorems.Thm_CyclotomicIntegers_equiv_zeta
-- name    : CyclotomicIntegers.equiv_zeta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:49.86072+00:00
-- url     : https://prove2.me/theorems/2bc7a46b-9f12-4e9c-92bf-0719ff9859d6
-- title:
--   Cyclotomic Integers: equiv zeta
-- statement:
--   The Cyclotomic Integers construction uses the equiv zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L60-L62

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

theorem CyclotomicIntegers.equiv_zeta : equiv p (zeta p) = (IsCyclotomicExtension.zeta_spec
    p ℚ (CyclotomicField p ℚ)).toInteger := by sorry
