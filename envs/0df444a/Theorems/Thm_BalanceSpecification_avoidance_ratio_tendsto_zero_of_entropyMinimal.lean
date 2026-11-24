-- Prove2me | Theorems.Thm_BalanceSpecification_avoidance_ratio_tendsto_zero_of_entropyMinimal
-- name    : BalanceSpecification.avoidance_ratio_tendsto_zero_of_entropyMinimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:09:15.891059+00:00
-- url     : https://prove2.me/theorems/cf4ec48a-b095-49de-b4ae-8fafe1ab160b
-- title:
--   Balance Specification: avoidance ratio tendsto zero of entropy Minimal
-- statement:
--   Entropy minimality forces the relative number of words avoiding a fixed
--   admissible word to tend to zero. No entropy gap is assumed.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyMinimal.lean#L78-L102
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyMinimal.lean#L78-L102

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

theorem BalanceSpecification.avoidance_ratio_tendsto_zero_of_entropyMinimal {X : ShiftSpace A}
    (hEM : EntropyMinimal X) {v : Word A} (hv : v ∈ language X) :
    Tendsto (fun n : ℕ =>
      (wordCount (avoidingLanguage (language X) v) n : ℝ) / wordCount (language X) n)
      atTop (𝓝 0) := by sorry
