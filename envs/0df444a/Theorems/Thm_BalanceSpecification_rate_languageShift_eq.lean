-- Prove2me | Theorems.Thm_BalanceSpecification_rate_languageShift_eq
-- name    : BalanceSpecification.rate_languageShift_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:08:41.96422+00:00
-- url     : https://prove2.me/theorems/7c6171cf-0883-47f0-acc9-b13de916e3db
-- title:
--   Balance Specification: rate language Shift eq
-- statement:
--   The real growth rates of a factorial language and its associated shift agree
--   whenever the language has words of every length.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L307-L345
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L307-L345

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

theorem BalanceSpecification.rate_languageShift_eq {L : Set (Word A)} (hL : IsFactorial L)
    (hpos : ∀ n, 0 < wordCount L n) :
    Growth.rate (fun n => (wordCount L n : ℝ)) =
      Growth.rate (fun n => (wordCount (language (languageShift L)) n : ℝ)) := by sorry
