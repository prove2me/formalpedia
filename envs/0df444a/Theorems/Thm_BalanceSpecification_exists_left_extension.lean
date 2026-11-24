-- Prove2me | Theorems.Thm_BalanceSpecification_exists_left_extension
-- name    : BalanceSpecification.exists_left_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:53:42.735269+00:00
-- url     : https://prove2.me/theorems/bccf2c58-1a90-434d-a0b2-29f3e697af06
-- title:
--   Balance Specification: exists left extension
-- statement:
--   A word in a two-sided shift admits a left extension of any length.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L70-L74
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L70-L74

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

theorem BalanceSpecification.exists_left_extension {w : Word A} (hw : w ∈ language X) (n : ℕ) :
    ∃ v : Word A, v.length = n ∧ v ++ w ∈ language X := by sorry
