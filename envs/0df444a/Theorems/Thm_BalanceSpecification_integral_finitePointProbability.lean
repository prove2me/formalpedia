-- Prove2me | Theorems.Thm_BalanceSpecification_integral_finitePointProbability
-- name    : BalanceSpecification.integral_finitePointProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:48:18.857822+00:00
-- url     : https://prove2.me/theorems/50b69afb-94db-40c2-ae6d-67c9e7014110
-- title:
--   Balance Specification: integral finite Point Probability
-- statement:
--   The Balance Specification construction uses the integral finite Point Probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L61-L67
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L61-L67

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

theorem BalanceSpecification.integral_finitePointProbability [MeasurableSingletonClass Ω]
    (x : I → Ω) (f : Ω → ℝ) :
    ∫ y, f y ∂(finitePointProbability x : Measure Ω) =
      (Fintype.card I : ℝ)⁻¹ * ∑ i : I, f (x i) := by sorry
