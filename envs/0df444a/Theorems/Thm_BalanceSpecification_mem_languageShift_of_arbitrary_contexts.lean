-- Prove2me | Theorems.Thm_BalanceSpecification_mem_languageShift_of_arbitrary_contexts
-- name    : BalanceSpecification.mem_languageShift_of_arbitrary_contexts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:48:13.628804+00:00
-- url     : https://prove2.me/theorems/815e26f1-00c9-483c-9c49-9d7ec2246a33
-- title:
--   Balance Specification: mem language Shift of arbitrary contexts
-- statement:
--   Arbitrarily large symmetric admissible neighborhoods of a word yield a
--   configuration of the associated shift in which the word occurs.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L110-L149
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L110-L149

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

theorem BalanceSpecification.mem_languageShift_of_arbitrary_contexts [Nonempty A]
    {L : Set (Word A)} (hL : IsFactorial L) {w : Word A}
    (hw : ∀ M : ℕ, ∃ p q : Word A,
      M ≤ p.length ∧ M ≤ q.length ∧ p ++ w ++ q ∈ L) :
    w ∈ language (languageShift L) := by sorry
