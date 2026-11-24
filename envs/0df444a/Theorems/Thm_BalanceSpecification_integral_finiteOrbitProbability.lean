-- Prove2me | Theorems.Thm_BalanceSpecification_integral_finiteOrbitProbability
-- name    : BalanceSpecification.integral_finiteOrbitProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:48:23.832801+00:00
-- url     : https://prove2.me/theorems/77d13ce6-8a94-4c39-9f5c-987e43e3fa95
-- title:
--   Balance Specification: integral finite Orbit Probability
-- statement:
--   The Balance Specification construction uses the integral finite Orbit Probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L79-L88
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L79-L88

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

theorem BalanceSpecification.integral_finiteOrbitProbability [MeasurableSingletonClass Ω]
    (f : Ω → Ω) (x : I → Ω) (n : ℕ) (g : Ω → ℝ) :
    ∫ y, g y ∂(finiteOrbitProbability f x n : Measure Ω) =
      (Fintype.card I : ℝ)⁻¹ * ∑ i : I, birkhoffAverage ℝ f g (n + 1) (x i) := by sorry
