-- Prove2me | Theorems.Thm_BalanceSpecification_mem_language_iff_exists_block_zero
-- name    : BalanceSpecification.mem_language_iff_exists_block_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:16.607065+00:00
-- url     : https://prove2.me/theorems/9dd7ca81-cc81-4cc7-bdc7-ae866a943dde
-- title:
--   Balance Specification: mem language iff exists block zero
-- statement:
--   Every word can be realized starting at the origin.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L48-L55
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L48-L55

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

theorem BalanceSpecification.mem_language_iff_exists_block_zero {w : Word A} :
    w ∈ language X ↔ ∃ x ∈ X.carrier, block x 0 w.length = w := by sorry
