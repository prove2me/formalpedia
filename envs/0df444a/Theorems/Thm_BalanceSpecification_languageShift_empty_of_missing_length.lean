-- Prove2me | Theorems.Thm_BalanceSpecification_languageShift_empty_of_missing_length
-- name    : BalanceSpecification.languageShift_empty_of_missing_length
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:08:31.667846+00:00
-- url     : https://prove2.me/theorems/5c780322-537b-4657-9c3d-e1346b05147f
-- title:
--   Balance Specification: language Shift empty of missing length
-- statement:
--   A factorial language with a missing length generates the empty shift.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L228-L235
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L228-L235

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

theorem BalanceSpecification.languageShift_empty_of_missing_length {L : Set (Word A)}
    {n : ℕ} (hn : wordCount L n = 0) : (languageShift L).carrier = ∅ := by sorry
