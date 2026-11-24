-- Prove2me | Theorems.Thm_BalanceSpecification_mem_languageShift_iff
-- name    : BalanceSpecification.mem_languageShift_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:19.416095+00:00
-- url     : https://prove2.me/theorems/92a5cf5f-1bde-4b1f-b90f-7ca322f1e727
-- title:
--   Balance Specification: mem language Shift iff
-- statement:
--   The Balance Specification construction uses the mem language Shift iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L68-L77
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L68-L77

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

theorem BalanceSpecification.mem_languageShift_iff {L : Set (Word A)} {x : Configuration A} :
    x ∈ (languageShift L).carrier ↔ ∀ k n, block x k n ∈ L := by sorry
