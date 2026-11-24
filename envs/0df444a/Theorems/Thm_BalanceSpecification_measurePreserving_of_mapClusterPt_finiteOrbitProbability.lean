-- Prove2me | Theorems.Thm_BalanceSpecification_measurePreserving_of_mapClusterPt_finiteOrbitProbability
-- name    : BalanceSpecification.measurePreserving_of_mapClusterPt_finiteOrbitProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:39.436454+00:00
-- url     : https://prove2.me/theorems/e3791543-5275-42f5-a4f6-8b26d92b1046
-- title:
--   Balance Specification: measure Preserving of map Cluster Pt finite Orbit Probability
-- statement:
--   A weak cluster point of the finite orbit averages is invariant.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L176-L202
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L176-L202

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
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [T2Space Ω]
    [HasOuterApproxClosed Ω]
    {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, Nonempty (I n)]

theorem BalanceSpecification.measurePreserving_of_mapClusterPt_finiteOrbitProbability
    {f : Ω → Ω} (hf : Continuous f) (x : ∀ n, I n → Ω)
    {μ : ProbabilityMeasure Ω}
    (hμ : MapClusterPt μ atTop (fun n => finiteOrbitProbability f (x n) n)) :
    MeasurePreserving f (μ : Measure Ω) (μ : Measure Ω) := by sorry
