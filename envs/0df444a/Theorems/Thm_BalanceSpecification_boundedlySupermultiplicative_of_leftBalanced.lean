-- Prove2me | Theorems.Thm_BalanceSpecification_boundedlySupermultiplicative_of_leftBalanced
-- name    : BalanceSpecification.boundedlySupermultiplicative_of_leftBalanced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:44.917076+00:00
-- url     : https://prove2.me/theorems/ec6b537c-7cef-4831-a456-ee2fa6c84ea9
-- title:
--   Balance Specification: boundedly Supermultiplicative of left Balanced
-- statement:
--   The left-balanced version follows by reversal, with exactly the same word counts.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CountBounds.lean#L187-L193
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CountBounds.lean#L187-L193

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

theorem BalanceSpecification.boundedlySupermultiplicative_of_leftBalanced (hL : IsFactorial L)
    (h : LeftBalanced L) : BoundedlySupermultiplicative L := by sorry
