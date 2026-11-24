-- Prove2me | Theorems.Thm_BalanceSpecification_blocking_estimate
-- name    : BalanceSpecification.blocking_estimate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:07:08.278799+00:00
-- url     : https://prove2.me/theorems/f337c09d-9880-4f79-b1aa-81991f54d62a
-- title:
--   Balance Specification: blocking estimate
-- statement:
--   A convenient form with a harmless larger numerical constant.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockingEstimate.lean#L136-L144
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockingEstimate.lean#L136-L144

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

theorem BalanceSpecification.blocking_estimate {C : ℝ} (hC : 0 ≤ C)
    (hnonneg : ∀ s l, 0 ≤ H s l)
    (hsub : ∀ s a b, H s (a + b) ≤ H s a + H (s + a) b)
    (hbound : ∀ s l, H s l ≤ (l : ℝ) * C)
    {n N : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    (n : ℝ) * H 0 N ≤ (∑ i ∈ Finset.range N, H i n) + 3 * (n : ℝ)^2 * C := by sorry
