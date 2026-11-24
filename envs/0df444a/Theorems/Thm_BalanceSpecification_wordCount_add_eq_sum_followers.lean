-- Prove2me | Theorems.Thm_BalanceSpecification_wordCount_add_eq_sum_followers
-- name    : BalanceSpecification.wordCount_add_eq_sum_followers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:38.555109+00:00
-- url     : https://prove2.me/theorems/f4bf9c86-a1f8-47ab-a1b6-81bae35a30ca
-- title:
--   Balance Specification: word Count add eq sum followers
-- statement:
--   Each prefix contributes exactly its number of followers to the next word count.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CountBounds.lean#L44-L76
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CountBounds.lean#L44-L76

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

theorem BalanceSpecification.wordCount_add_eq_sum_followers (hL : IsFactorial L) (m n : ℕ) :
    wordCount L (m + n) = ∑ u ∈ wordFinset L m, (followerFinset L u n).card := by sorry
