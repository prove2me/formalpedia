-- Prove2me | Theorems.Thm_BalanceSpecification_wordCount_add_le
-- name    : BalanceSpecification.wordCount_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:33:21.91583+00:00
-- url     : https://prove2.me/theorems/5dea176c-60cd-40f3-93ed-5a30e4283e9e
-- title:
--   Balance Specification: word Count add le
-- statement:
--   Splitting an admissible word gives an injective map into pairs of admissible words.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CountBounds.lean#L20-L41
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CountBounds.lean#L20-L41

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CountBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}

theorem BalanceSpecification.wordCount_add_le (hL : IsFactorial L) (m n : ℕ) :
    wordCount L (m + n) ≤ wordCount L m * wordCount L n := by sorry
