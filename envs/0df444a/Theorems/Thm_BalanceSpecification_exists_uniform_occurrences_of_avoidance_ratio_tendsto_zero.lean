-- Prove2me | Theorems.Thm_BalanceSpecification_exists_uniform_occurrences_of_avoidance_ratio_tendsto_zero
-- name    : BalanceSpecification.exists_uniform_occurrences_of_avoidance_ratio_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:08:46.031047+00:00
-- url     : https://prove2.me/theorems/2e9969df-e0a5-4047-852f-d1937f408961
-- title:
--   Balance Specification: exists uniform occurrences of avoidance ratio tendsto zero
-- statement:
--   The same positive extension length works for both sides and every initial
--   word once the avoidance ratio tends to zero.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L78-L96
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L78-L96

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

theorem BalanceSpecification.exists_uniform_occurrences_of_avoidance_ratio_tendsto_zero
    (hB : BiBalanced L) (v : Word A)
    (hrare : Tendsto
      (fun n : ℕ => (wordCount (avoidingLanguage L v) n : ℝ) / wordCount L n)
      atTop (𝓝 0)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ u ∈ L,
      (∃ s ∈ followerFinset L u N, v <:+: s) ∧
      (∃ p ∈ predecessorFinset L u N, v <:+: p) := by sorry
