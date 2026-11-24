-- Prove2me | Theorems.Thm_BalanceSpecification_block_prefix_tiles_suffix_le
-- name    : BalanceSpecification.block_prefix_tiles_suffix_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:05.529173+00:00
-- url     : https://prove2.me/theorems/e307c79d-04e7-43ae-b521-b23a2a9ff5ca
-- title:
--   Balance Specification: block prefix tiles suffix le
-- statement:
--   Splitting into a prefix, equal blocks, and a suffix.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockingEstimate.lean#L73-L83
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockingEstimate.lean#L73-L83

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

theorem BalanceSpecification.block_prefix_tiles_suffix_le (hzero : ∀ s, H s 0 = 0)
    (hsub : ∀ s a b, H s (a + b) ≤ H s a + H (s + a) b)
    {r n k N : ℕ} (hfit : r + k * n ≤ N) :
    H 0 N ≤ H 0 r + (∑ j ∈ Finset.range k, H (r + j * n) n) +
      H (r + k * n) (N - (r + k * n)) := by sorry
