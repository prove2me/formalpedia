-- Prove2me | Theorems.Thm_CyclotomicIntegers_powerBasis_dim
-- name    : CyclotomicIntegers.powerBasis_dim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:59.765975+00:00
-- url     : https://prove2.me/theorems/523f976f-f349-4ed4-8534-c2ba9c150948
-- title:
--   Cyclotomic Integers: power Basis dim
-- statement:
--   The Cyclotomic Integers construction uses the power Basis dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L104-L105
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L104-L105

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

theorem CyclotomicIntegers.powerBasis_dim : (powerBasis p).dim = p - 1 := by sorry
