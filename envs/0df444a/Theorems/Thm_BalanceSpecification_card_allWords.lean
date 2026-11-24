-- Prove2me | Theorems.Thm_BalanceSpecification_card_allWords
-- name    : BalanceSpecification.card_allWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:43:19.075637+00:00
-- url     : https://prove2.me/theorems/c893a978-d1da-48fd-8f5e-2e9a498f6ff4
-- title:
--   Balance Specification: card all Words
-- statement:
--   The finite set of unrestricted length-`n` words has the expected cardinality.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TilingBounds.lean#L46-L56
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TilingBounds.lean#L46-L56

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TilingBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A]

theorem BalanceSpecification.card_allWords (n : ℕ) : (allWords (A := A) n).card = (Fintype.card A) ^ n := by sorry
