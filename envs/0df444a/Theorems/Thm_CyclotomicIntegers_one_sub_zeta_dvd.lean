-- Prove2me | Theorems.Thm_CyclotomicIntegers_one_sub_zeta_dvd
-- name    : CyclotomicIntegers.one_sub_zeta_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:52.317801+00:00
-- url     : https://prove2.me/theorems/ed1418a9-b313-48db-89c0-06fa31f23654
-- title:
--   Cyclotomic Integers: one sub zeta dvd
-- statement:
--   The Cyclotomic Integers construction uses the one sub zeta dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean#L84-L85

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

theorem CyclotomicIntegers.one_sub_zeta_dvd : 1 - zeta p ∣ p := by sorry
