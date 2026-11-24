-- Prove2me | Theorems.Thm_BalanceSpecification_wordCount_eq_zero_of_le_missing
-- name    : BalanceSpecification.wordCount_eq_zero_of_le_missing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:08:33.994118+00:00
-- url     : https://prove2.me/theorems/5f891135-9b32-4e32-bfb3-485a8e9ef95a
-- title:
--   Balance Specification: word Count eq zero of le missing
-- statement:
--   If a length is missing from a factorial language, all larger lengths are missing.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L214-L225
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L214-L225

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

theorem BalanceSpecification.wordCount_eq_zero_of_le_missing {L : Set (Word A)} (hL : IsFactorial L)
    {n N : ℕ} (hnN : n ≤ N) (hn : wordCount L n = 0) : wordCount L N = 0 := by sorry
