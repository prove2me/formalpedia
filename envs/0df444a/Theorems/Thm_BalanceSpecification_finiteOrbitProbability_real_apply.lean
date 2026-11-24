-- Prove2me | Theorems.Thm_BalanceSpecification_finiteOrbitProbability_real_apply
-- name    : BalanceSpecification.finiteOrbitProbability_real_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:48:22.638493+00:00
-- url     : https://prove2.me/theorems/2d1191e8-4b55-4a86-8ac2-6dd6b801e989
-- title:
--   Balance Specification: finite Orbit Probability real apply
-- statement:
--   The Balance Specification construction uses the finite Orbit Probability real apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L90-L101
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L90-L101

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

theorem BalanceSpecification.finiteOrbitProbability_real_apply [MeasurableSingletonClass Ω]
    (f : Ω → Ω) (x : I → Ω) (n : ℕ) {E : Set Ω} (hE : MeasurableSet E) :
    (finiteOrbitProbability f x n : Measure Ω).real E =
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j : Fin (n + 1),
        (finitePointProbability (fun i => f^[j.val] (x i)) : Measure Ω).real E := by sorry
