-- Prove2me | Theorems.Thm_BalanceSpecification_carrier_eq_of_language_eq
-- name    : BalanceSpecification.carrier_eq_of_language_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:17:01.364071+00:00
-- url     : https://prove2.me/theorems/bf442059-2588-4727-8cc4-dde3e8e91cee
-- title:
--   Balance Specification: carrier eq of language eq
-- statement:
--   Closed shift spaces with the same finite words have the same configurations.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L134-L138
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L134-L138

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

theorem BalanceSpecification.carrier_eq_of_language_eq {Y : ShiftSpace A}
    (h : language X = language Y) : X.carrier = Y.carrier := by sorry
