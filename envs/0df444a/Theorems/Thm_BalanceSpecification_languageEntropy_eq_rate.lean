-- Prove2me | Theorems.Thm_BalanceSpecification_languageEntropy_eq_rate
-- name    : BalanceSpecification.languageEntropy_eq_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:43:44.849268+00:00
-- url     : https://prove2.me/theorems/4fcfbc43-5b11-416f-962e-3c3e5b99b228
-- title:
--   Balance Specification: language Entropy eq rate
-- statement:
--   On factorial languages with words of all lengths, the extended limsup
--   coincides with the actual real Fekete growth rate.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L259-L277
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L259-L277

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

theorem BalanceSpecification.languageEntropy_eq_rate {L : Set (Word A)} (hL : IsFactorial L)
    (hpos : ∀ n, 0 < wordCount L n) :
    languageEntropy L = (Growth.rate (fun n => (wordCount L n : ℝ)) : EReal) := by sorry
