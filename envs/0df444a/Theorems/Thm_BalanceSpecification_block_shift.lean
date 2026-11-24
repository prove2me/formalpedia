-- Prove2me | Theorems.Thm_BalanceSpecification_block_shift
-- name    : BalanceSpecification.block_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:04.775717+00:00
-- url     : https://prove2.me/theorems/86fedee0-352b-4aae-aa5e-6d37a31eae90
-- title:
--   Balance Specification: block shift
-- statement:
--   Translating a configuration translates the starting coordinate of a block.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L28-L30
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L28-L30

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}

theorem BalanceSpecification.block_shift (x : Configuration A) (k l : ℤ) (n : ℕ) :
    block (SymbolicDynamics.FullShift.shift k x) l n = block x (k + l) n := by sorry
