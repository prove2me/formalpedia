-- Prove2me | Theorems.Thm_BalanceSpecification_block_append
-- name    : BalanceSpecification.block_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:31:54.751171+00:00
-- url     : https://prove2.me/theorems/41ecd405-6c2c-49e8-b009-eb6d2cf9e067
-- title:
--   Balance Specification: block append
-- statement:
--   Splitting a contiguous block at a prescribed length.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L22-L25
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L22-L25

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}

theorem BalanceSpecification.block_append (x : Configuration A) (k : ℤ) (m n : ℕ) :
    block x k (m + n) = block x k m ++ block x (k + m) n := by sorry
