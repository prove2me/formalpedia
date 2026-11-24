-- Prove2me | Theorems.Thm_BalanceSpecification_uniform_occurrences_of_entropyMinimal_biBalanced
-- name    : BalanceSpecification.uniform_occurrences_of_entropyMinimal_biBalanced
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:09:25.047934+00:00
-- url     : https://prove2.me/theorems/38cb7a64-2b1a-48a1-a1fa-43eb73616e2a
-- title:
--   Balance Specification: uniform occurrences of entropy Minimal bi Balanced
-- statement:
--   The source's uniform-occurrence lemma. A single positive length works for
--   both predecessors and followers, for every initial word.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyMinimal.lean#L106-L113
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyMinimal.lean#L106-L113

module
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Definitions.Def_BalanceSpecificaton_Occurrence
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]

theorem BalanceSpecification.uniform_occurrences_of_entropyMinimal_biBalanced {X : ShiftSpace A}
    (hEM : EntropyMinimal X) (hB : BiBalanced (language X))
    (v : Word A) (hv : v ∈ language X) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ u ∈ language X,
      (∃ s ∈ followerFinset (language X) u N, v <:+: s) ∧
      (∃ p ∈ predecessorFinset (language X) u N, v <:+: p) := by sorry
