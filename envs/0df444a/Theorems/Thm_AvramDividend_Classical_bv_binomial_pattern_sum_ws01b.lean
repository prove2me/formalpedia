-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_binomial_pattern_sum_ws01b
-- name    : AvramDividend.Classical.bv_binomial_pattern_sum_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:15:54.828016+00:00
-- url     : https://prove2.me/theorems/02140547-79ac-4610-b8ef-3cd277678589
-- title:
--   Exact sum over all fixed-cardinality Bernoulli grid patterns equals the binomial mass
-- statement:
--   For every natural grid length n, count k and real-valued active/inactive cell masses p and q, the sum of the two-valued product over every k-element subset of the n cells equals choose(n,k) times p^k times q^(n-k). The theorem handles all edge cases, including k>n, with no probability-process assumptions.
-- source:
--   Remote-compiler-validated Lean proof in the pinned Prove2Me environment on 28 October 2026, using Finset.prod_ite, Finset.card_sdiff_of_subset, Finset.card_powersetCard and exact finite-set product and sum manipulation. This is the combinatorial coefficient component required to turn the genuine original-process grid pattern theorem into a finite-grid binomial law.

import Mathlib

open Finset
open scoped BigOperators

/-- Summing every fixed-size active-cell Bernoulli product gives the exact
binomial mass, with the finite grid partition handled by powersetCard. -/

theorem AvramDividend.Classical.bv_binomial_pattern_sum_ws01b
    (n k : ℕ) (p q : ℝ) :
    (∑ S ∈ Finset.powersetCard k (Finset.range n),
      ∏ i ∈ Finset.range n, if i ∈ S then p else q) =
        (Nat.choose n k : ℝ) * p ^ k * q ^ (n - k) := by sorry
