-- Prove2me | Theorems.Thm_BalanceSpecification_languageEntropy_eq_bot_of_missing_length
-- name    : BalanceSpecification.languageEntropy_eq_bot_of_missing_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:48:07.535652+00:00
-- url     : https://prove2.me/theorems/a39c0e19-af96-4b4b-9f08-18925bb3b947
-- title:
--   Balance Specification: language Entropy eq bot of missing length
-- statement:
--   A missing length forces extended language entropy to be minus infinity.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L281-L297
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L281-L297

module
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_GrowthTiling
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open scoped ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A]
omit [TopologicalSpace A] [DiscreteTopology A]

theorem BalanceSpecification.languageEntropy_eq_bot_of_missing_length {L : Set (Word A)}
    (hL : IsFactorial L) {N : ℕ} (hN : wordCount L N = 0) : languageEntropy L = ⊥ := by sorry
