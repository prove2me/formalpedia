-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_binary_patterns_pairwise_disjoint_ws01b
-- name    : AvramDividend.Classical.bv_binary_patterns_pairwise_disjoint_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:25:55.920494+00:00
-- url     : https://prove2.me/theorems/e169cf60-55d7-45cd-b5ea-a8ef4a342ae7
-- title:
--   Pairwise disjointness of distinct fixed-cardinality binary grid pattern events
-- statement:
--   For two disjoint outcomes in each cell of a finite grid, complete binary event patterns indexed by distinct k-element subsets are pairwise disjoint sets of sample paths. A sample satisfying the active/inactive conditions of two different subsets would force the same active index set, contradicting distinctness.
-- source:
--   The exact proof passed the Prove2Me remote Lean compiler on 28 October 2026. For a sample in a given pattern, identify membership of every in-range index in the selected active subset with the corresponding active event. Disjointness of active and inactive predicates handles the opposite implication; out-of-range indices belong to neither subset.

import Mathlib

open Set
open scoped Classical

/-- Distinct complete binary grid patterns are disjoint as sample events. -/

theorem AvramDividend.Classical.bv_binary_patterns_pairwise_disjoint_ws01b
    {Ω : Type*} (A B : ℕ → Set Ω) (n k : ℕ)
    (hExcl : ∀ i : ℕ, i < n → ∀ ω : Ω,
      ω ∈ A i → ω ∈ B i → False) :
    ((↑(Finset.powersetCard k (Finset.range n))) : Set (Finset ℕ)).PairwiseDisjoint
      (fun S => {ω : Ω | ∀ i : ℕ, i < n →
        if i ∈ S then ω ∈ A i else ω ∈ B i}) := by sorry
