-- Prove2me | Theorems.Thm_BalanceSpecification_block_chain_le
-- name    : BalanceSpecification.block_chain_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:59.560452+00:00
-- url     : https://prove2.me/theorems/600e7480-808b-4f12-bc78-3bdb9260db77
-- title:
--   Balance Specification: block chain le
-- statement:
--   Subadditivity along a chain of equal-length adjacent intervals.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockingEstimate.lean#L20-L27
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockingEstimate.lean#L20-L27

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {H : ℕ → ℕ → ℝ}

theorem BalanceSpecification.block_chain_le (hzero : ∀ s, H s 0 = 0)
    (hsub : ∀ s a b, H s (a + b) ≤ H s a + H (s + a) b) (s n k : ℕ) :
    H s (k * n) ≤ ∑ j ∈ Finset.range k, H (s + j * n) n := by sorry
