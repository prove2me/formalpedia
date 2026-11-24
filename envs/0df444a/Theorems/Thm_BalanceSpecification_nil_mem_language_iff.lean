-- Prove2me | Theorems.Thm_BalanceSpecification_nil_mem_language_iff
-- name    : BalanceSpecification.nil_mem_language_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:33:28.895203+00:00
-- url     : https://prove2.me/theorems/dd951498-9a24-48b1-bfd1-99cdc9075bc0
-- title:
--   Balance Specification: nil mem language iff
-- statement:
--   The empty word belongs precisely to nonempty shifts.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L40-L45
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L40-L45

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

theorem BalanceSpecification.nil_mem_language_iff : ([] : Word A) ∈ language X ↔ X.carrier.Nonempty := by sorry
