-- Prove2me | Theorems.Thm_BalanceSpecification_leftBalanced_of_bounded_bridges
-- name    : BalanceSpecification.leftBalanced_of_bounded_bridges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:53:50.273418+00:00
-- url     : https://prove2.me/theorems/fa84585d-dca6-4e6f-83b2-a7d6b10954f2
-- title:
--   Balance Specification: left Balanced of bounded bridges
-- statement:
--   Reversing bounded bridges gives the corresponding left-balanced estimate.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Specification.lean#L105-L124
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Specification.lean#L105-L124

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

theorem BalanceSpecification.leftBalanced_of_bounded_bridges (hL : IsFactorial L)
    (hpos : ∀ n, 0 < wordCount L n) {N : ℕ}
    (hbridge : ∀ u ∈ L, ∀ v ∈ L,
      ∃ w : Word A, w.length ≤ N ∧ u ++ w ++ v ∈ L) : LeftBalanced L := by sorry
