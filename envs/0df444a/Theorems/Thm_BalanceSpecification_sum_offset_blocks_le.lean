-- Prove2me | Theorems.Thm_BalanceSpecification_sum_offset_blocks_le
-- name    : BalanceSpecification.sum_offset_blocks_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:06:56.263268+00:00
-- url     : https://prove2.me/theorems/b94f0ce9-a9ac-427d-be80-b84ed51d43d8
-- title:
--   Balance Specification: sum offset blocks le
-- statement:
--   Each interval in all residue-class tilings has a distinct starting position.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockingEstimate.lean#L30-L70
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockingEstimate.lean#L30-L70

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

theorem BalanceSpecification.sum_offset_blocks_le (hnonneg : ∀ s l, 0 ≤ H s l)
    {n k N : ℕ} (hn : 0 < n) (hkn : k * n ≤ N) :
    (∑ r ∈ Finset.range n, ∑ j ∈ Finset.range k, H (r + j * n) n) ≤
      ∑ i ∈ Finset.range N, H i n := by sorry
