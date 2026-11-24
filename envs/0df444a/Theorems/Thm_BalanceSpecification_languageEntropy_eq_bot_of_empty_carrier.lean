-- Prove2me | Theorems.Thm_BalanceSpecification_languageEntropy_eq_bot_of_empty_carrier
-- name    : BalanceSpecification.languageEntropy_eq_bot_of_empty_carrier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:09:16.2939+00:00
-- url     : https://prove2.me/theorems/e9a52119-03d8-4aa1-935a-18ba92afd5a9
-- title:
--   Balance Specification: language Entropy eq bot of empty carrier
-- statement:
--   The language of an empty shift has entropy minus infinity.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyMinimal.lean#L30-L38
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyMinimal.lean#L30-L38

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
omit [DiscreteTopology A]

theorem BalanceSpecification.languageEntropy_eq_bot_of_empty_carrier {X : ShiftSpace A}
    (hX : X.carrier = ∅) : languageEntropy (language X) = ⊥ := by sorry
