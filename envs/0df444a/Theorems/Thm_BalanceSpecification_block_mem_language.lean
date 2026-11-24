-- Prove2me | Theorems.Thm_BalanceSpecification_block_mem_language
-- name    : BalanceSpecification.block_mem_language
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:31:25.963209+00:00
-- url     : https://prove2.me/theorems/9ce8c6db-3725-41b2-90ea-15480511bf26
-- title:
--   Balance Specification: block mem language
-- statement:
--   A block cut from a configuration of a shift belongs to its language.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L35-L37
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L35-L37

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

theorem BalanceSpecification.block_mem_language {x : Configuration A} (hx : x ∈ X.carrier)
    (k : ℤ) (n : ℕ) : block x k n ∈ language X := by sorry
