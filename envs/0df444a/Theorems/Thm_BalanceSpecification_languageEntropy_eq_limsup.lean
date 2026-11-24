-- Prove2me | Theorems.Thm_BalanceSpecification_languageEntropy_eq_limsup
-- name    : BalanceSpecification.languageEntropy_eq_limsup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:40:25.334807+00:00
-- url     : https://prove2.me/theorems/91dad79f-3577-4b85-85e3-afd101f41fe9
-- title:
--   Balance Specification: language Entropy eq limsup
-- statement:
--   Shifting the sequence to positive lengths does not change the manuscript's limsup.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L246-L254
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean#L246-L254

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

theorem BalanceSpecification.languageEntropy_eq_limsup (L : Set (Word A)) :
    languageEntropy L = Filter.limsup (fun n : ℕ =>
      ((((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log ((wordCount L n : ℕ) : ℝ≥0∞)))
        Filter.atTop := by sorry
