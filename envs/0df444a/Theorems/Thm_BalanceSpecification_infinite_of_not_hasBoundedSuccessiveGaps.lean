-- Prove2me | Theorems.Thm_BalanceSpecification_infinite_of_not_hasBoundedSuccessiveGaps
-- name    : BalanceSpecification.infinite_of_not_hasBoundedSuccessiveGaps
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:58:30.725212+00:00
-- url     : https://prove2.me/theorems/b2ea8c98-3271-4960-b0e6-067d0d612fe4
-- title:
--   Balance Specification: infinite of not has Bounded Successive Gaps
-- statement:
--   In particular, unbounded successive gaps require infinitely many members.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBounds.lean#L96-L101
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBounds.lean#L96-L101

module
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification

theorem BalanceSpecification.infinite_of_not_hasBoundedSuccessiveGaps {S : Set ℕ}
    (hS : ¬HasBoundedSuccessiveGaps S) : S.Infinite := by sorry
