-- Prove2me | Theorems.Thm_BalanceSpecification_mem_carrier_iff_blocks
-- name    : BalanceSpecification.mem_carrier_iff_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:59.905046+00:00
-- url     : https://prove2.me/theorems/0652c0b3-39ab-4a05-899f-1adb4080e12d
-- title:
--   Balance Specification: mem carrier iff blocks
-- statement:
--   A closed shift space is recovered from its finite contiguous blocks.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L109-L123
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L109-L123

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

theorem BalanceSpecification.mem_carrier_iff_blocks {x : Configuration A} :
    x ∈ X.carrier ↔ ∀ k n, block x k n ∈ language X := by sorry
