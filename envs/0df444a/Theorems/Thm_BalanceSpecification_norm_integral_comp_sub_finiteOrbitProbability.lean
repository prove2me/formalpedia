-- Prove2me | Theorems.Thm_BalanceSpecification_norm_integral_comp_sub_finiteOrbitProbability
-- name    : BalanceSpecification.norm_integral_comp_sub_finiteOrbitProbability
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:07:32.720806+00:00
-- url     : https://prove2.me/theorems/09f1f619-b989-4dc1-8c4f-bd1daad360ca
-- title:
--   Balance Specification: norm integral comp sub finite Orbit Probability
-- statement:
--   The Balance Specification construction uses the norm integral comp sub finite Orbit Probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L123-L152
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L123-L152

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

theorem BalanceSpecification.norm_integral_comp_sub_finiteOrbitProbability [MeasurableSingletonClass Ω]
    [TopologicalSpace Ω] (f : Ω → Ω) (x : I → Ω) (n : ℕ) (g : Ω →ᵇ ℝ) :
    ‖(∫ y, (g ∘ f) y ∂(finiteOrbitProbability f x n : Measure Ω)) -
        ∫ y, g y ∂(finiteOrbitProbability f x n : Measure Ω)‖ ≤
      2 * ‖g‖ / (n + 1 : ℕ) := by sorry
