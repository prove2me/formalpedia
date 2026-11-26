-- Prove2me | Theorems.Thm_CSeparatedNPComplete_sum_mul_nonneg_of_antitone_of_prefix_nonneg
-- name    : CSeparatedNPComplete.sum_mul_nonneg_of_antitone_of_prefix_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:45:59.122487+00:00
-- url     : https://prove2.me/theorems/9245da24-e9f2-5b3d-b692-3dbdad458bd8
-- title:
--   CSeparated NPComplete: sum mul nonneg of antitone of prefix nonneg
-- statement:
--   Decreasing weights pair nonnegatively with a finite vector whose partial
--   sums are nonnegative and whose total sum vanishes.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/WeightedSum.lean#L51-L70
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/WeightedSum.lean#L51-L70

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

theorem CSeparatedNPComplete.sum_mul_nonneg_of_antitone_of_prefix_nonneg {n : ℕ}
    (a c : Fin n → ℝ) (hc : Antitone c)
    (ha : ∀ k : ℕ, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i)
    (ht : ∑ i, a i = 0) :
    0 ≤ ∑ i, c i * a i := by sorry
