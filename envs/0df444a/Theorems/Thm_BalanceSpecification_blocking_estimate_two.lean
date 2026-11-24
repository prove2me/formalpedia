-- Prove2me | Theorems.Thm_BalanceSpecification_blocking_estimate_two
-- name    : BalanceSpecification.blocking_estimate_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:11.084468+00:00
-- url     : https://prove2.me/theorems/dd9990b0-34f0-4a1b-87ee-7624d667594b
-- title:
--   Balance Specification: blocking estimate two
-- statement:
--   Averaging interval tilings loses at most two boundary blocks per residue class.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockingEstimate.lean#L86-L133
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockingEstimate.lean#L86-L133

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

theorem BalanceSpecification.blocking_estimate_two {C : ℝ} (hC : 0 ≤ C)
    (hnonneg : ∀ s l, 0 ≤ H s l)
    (hsub : ∀ s a b, H s (a + b) ≤ H s a + H (s + a) b)
    (hbound : ∀ s l, H s l ≤ (l : ℝ) * C)
    {n N : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    (n : ℝ) * H 0 N ≤ (∑ i ∈ Finset.range N, H i n) + 2 * (n : ℝ)^2 * C := by sorry
