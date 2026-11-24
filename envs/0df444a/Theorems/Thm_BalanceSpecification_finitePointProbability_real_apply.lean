-- Prove2me | Theorems.Thm_BalanceSpecification_finitePointProbability_real_apply
-- name    : BalanceSpecification.finitePointProbability_real_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:48:16.169329+00:00
-- url     : https://prove2.me/theorems/5d6ff40d-89e1-4d34-bc2c-40f3778a63e9
-- title:
--   Balance Specification: finite Point Probability real apply
-- statement:
--   The Balance Specification construction uses the finite Point Probability real apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L55-L59
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L55-L59

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology ENNReal Classical BoundedContinuousFunction
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [Nonempty I]

theorem BalanceSpecification.finitePointProbability_real_apply (x : I → Ω) {E : Set Ω} (hE : MeasurableSet E) :
    (finitePointProbability x : Measure Ω).real E =
      ((Finset.univ.filter fun i : I => x i ∈ E).card : ℝ) / Fintype.card I := by sorry
