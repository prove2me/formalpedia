-- Prove2me | Theorems.Thm_BalanceSpecification_exists_right_extension
-- name    : BalanceSpecification.exists_right_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:58.807341+00:00
-- url     : https://prove2.me/theorems/b554c07b-28ef-46cb-b013-c012c8766bf2
-- title:
--   Balance Specification: exists right extension
-- statement:
--   A word in a two-sided shift admits a right extension of any length.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L63-L67
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L63-L67

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.exists_right_extension {w : Word A} (hw : w ∈ language X) (n : ℕ) :
    ∃ v : Word A, v.length = n ∧ w ++ v ∈ language X := by sorry
