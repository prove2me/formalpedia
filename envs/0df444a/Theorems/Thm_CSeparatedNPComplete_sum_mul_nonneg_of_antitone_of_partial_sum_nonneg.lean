-- Prove2me | Theorems.Thm_CSeparatedNPComplete_sum_mul_nonneg_of_antitone_of_partial_sum_nonneg
-- name    : CSeparatedNPComplete.sum_mul_nonneg_of_antitone_of_partial_sum_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:45:59.91929+00:00
-- url     : https://prove2.me/theorems/f805d508-0e11-414b-80be-11096f306cbd
-- title:
--   CSeparated NPComplete: sum mul nonneg of antitone of partial sum nonneg
-- statement:
--   Abel's summation inequality for a sequence with nonnegative partial sums
--   and zero total sum.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/WeightedSum.lean#L16-L30
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/WeightedSum.lean#L16-L30

module
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Definitions.Def_CSeparatedNPComplete_WeightedSum
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
open scoped BigOperators

theorem CSeparatedNPComplete.sum_mul_nonneg_of_antitone_of_partial_sum_nonneg
    (n : ℕ) (a c : ℕ → ℝ)
    (hc : ∀ i, i + 1 < n → c (i + 1) ≤ c i)
    (ha : ∀ k, k ≤ n → 0 ≤ ∑ i ∈ Finset.range k, a i)
    (ht : ∑ i ∈ Finset.range n, a i = 0) :
    0 ≤ ∑ i ∈ Finset.range n, c i * a i := by sorry
