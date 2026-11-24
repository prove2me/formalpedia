-- Prove2me | Theorems.Thm_BalanceSpecification_uniform_occurrences_of_avoiding_ratio_lt
-- name    : BalanceSpecification.uniform_occurrences_of_avoiding_ratio_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:08:47.898549+00:00
-- url     : https://prove2.me/theorems/8d38fb97-fa30-4dee-93a5-f87bb57ebdba
-- title:
--   Balance Specification: uniform occurrences of avoiding ratio lt
-- statement:
--   At one common length, a small avoidance ratio gives occurrences on both
--   sides of every word, using a common balancedness lower bound.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L61-L74
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L61-L74

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Occurrence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] {L : Set (Word A)}

theorem BalanceSpecification.uniform_occurrences_of_avoiding_ratio_lt {v : Word A} {N : ℕ} {c : ℝ}
    (hR : ∀ u ∈ L, c ≤ ((followerFinset L u N).card : ℝ) / wordCount L N)
    (hP : ∀ u ∈ L, c ≤ ((predecessorFinset L u N).card : ℝ) / wordCount L N)
    (hsmall : (wordCount (avoidingLanguage L v) N : ℝ) / wordCount L N < c) :
    ∀ u ∈ L,
      (∃ s ∈ followerFinset L u N, v <:+: s) ∧
      (∃ p ∈ predecessorFinset L u N, v <:+: p) := by sorry
