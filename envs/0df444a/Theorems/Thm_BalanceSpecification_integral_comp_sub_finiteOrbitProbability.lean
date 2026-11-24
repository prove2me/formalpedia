-- Prove2me | Theorems.Thm_BalanceSpecification_integral_comp_sub_finiteOrbitProbability
-- name    : BalanceSpecification.integral_comp_sub_finiteOrbitProbability
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:07:20.278721+00:00
-- url     : https://prove2.me/theorems/29e3dd6d-f1ba-491a-91b2-5749c0e4f361
-- title:
--   Balance Specification: integral comp sub finite Orbit Probability
-- statement:
--   The Balance Specification construction uses the integral comp sub finite Orbit Probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L103-L121
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L103-L121

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

theorem BalanceSpecification.integral_comp_sub_finiteOrbitProbability [MeasurableSingletonClass Ω]
    (f : Ω → Ω) (x : I → Ω) (n : ℕ) (g : Ω → ℝ) :
    (∫ y, (g ∘ f) y ∂(finiteOrbitProbability f x n : Measure Ω)) -
        ∫ y, g y ∂(finiteOrbitProbability f x n : Measure Ω) =
      (Fintype.card I : ℝ)⁻¹ * ∑ i : I,
        ((n + 1 : ℕ) : ℝ)⁻¹ * (g (f^[n + 1] (x i)) - g (x i)) := by sorry
