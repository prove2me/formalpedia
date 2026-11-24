-- Prove2me | Theorems.Thm_BalanceSpecification_codedShift_mono
-- name    : BalanceSpecification.codedShift_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:21:16.883457+00:00
-- url     : https://prove2.me/theorems/08020d10-a7be-4145-92eb-84813a3efadd
-- title:
--   Balance Specification: coded Shift mono
-- statement:
--   The Balance Specification construction uses the coded Shift mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Coded.lean#L80-L82
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Coded.lean#L80-L82

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Topology.Continuous
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Coded
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}

theorem BalanceSpecification.codedShift_mono [TopologicalSpace A] {C D : Set (Word A)} (hCD : C ⊆ D) :
    (codedShift C).carrier ⊆ (codedShift D).carrier := by sorry
