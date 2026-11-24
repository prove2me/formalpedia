-- Prove2me | Theorems.Thm_BalanceSpecification_real_bounds_of_mapClusterPt_of_isClopen
-- name    : BalanceSpecification.real_bounds_of_mapClusterPt_of_isClopen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:41.322222+00:00
-- url     : https://prove2.me/theorems/c6b5c89a-2b7a-43d5-958d-26f432343a01
-- title:
--   Balance Specification: real bounds of map Cluster Pt of is Clopen
-- statement:
--   Cylinder bounds pass to weak cluster limits because cylinders are clopen.
--   The constants are unchanged.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L219-L232
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L219-L232

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

theorem BalanceSpecification.real_bounds_of_mapClusterPt_of_isClopen
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω] {ν : ℕ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hμ : MapClusterPt μ atTop ν) {E : Set Ω} (hE : IsClopen E) {l r : ℝ}
    (hb : ∀ᶠ n : ℕ in atTop, l ≤ (ν n : Measure Ω).real E ∧
      (ν n : Measure Ω).real E ≤ r) :
    l ≤ (μ : Measure Ω).real E ∧ (μ : Measure Ω).real E ≤ r := by sorry
