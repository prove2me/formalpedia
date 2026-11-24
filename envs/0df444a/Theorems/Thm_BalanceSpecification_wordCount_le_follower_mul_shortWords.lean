-- Prove2me | Theorems.Thm_BalanceSpecification_wordCount_le_follower_mul_shortWords
-- name    : BalanceSpecification.wordCount_le_follower_mul_shortWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:53:49.378822+00:00
-- url     : https://prove2.me/theorems/472b059a-0cd2-4526-9f6e-8e2d3526acca
-- title:
--   Balance Specification: word Count le follower mul short Words
-- statement:
--   Bounded bridges encode every admissible length-`n` word by a follower of
--   length `n` and a remainder whose length is at most the bridge bound.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Specification.lean#L40-L72
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Specification.lean#L40-L72

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Specification
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}

theorem BalanceSpecification.wordCount_le_follower_mul_shortWords (hL : IsFactorial L)
    {N : ℕ} {u : Word A}
    (hbridge : ∀ v ∈ L, ∃ w : Word A, w.length ≤ N ∧ u ++ w ++ v ∈ L)
    (n : ℕ) :
    wordCount L n ≤ (followerFinset L u n).card * (shortWords (A := A) N).card := by sorry
