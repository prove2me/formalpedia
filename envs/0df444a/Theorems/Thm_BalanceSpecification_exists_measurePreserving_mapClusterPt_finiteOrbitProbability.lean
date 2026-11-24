-- Prove2me | Theorems.Thm_BalanceSpecification_exists_measurePreserving_mapClusterPt_finiteOrbitProbability
-- name    : BalanceSpecification.exists_measurePreserving_mapClusterPt_finiteOrbitProbability
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:43:52.726658+00:00
-- url     : https://prove2.me/theorems/9a5ede18-4831-4582-a508-4fbf125f7036
-- title:
--   Balance Specification: exists measure Preserving map Cluster Pt finite Orbit Probability
-- statement:
--   Compactness supplies an invariant cluster point of any such family.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L205-L213
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L205-L213

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

theorem BalanceSpecification.exists_measurePreserving_mapClusterPt_finiteOrbitProbability
    [CompactSpace Ω] {f : Ω → Ω} (hf : Continuous f)
    (x : ∀ n, I n → Ω) :
    ∃ μ : ProbabilityMeasure Ω,
      MapClusterPt μ atTop (fun n => finiteOrbitProbability f (x n) n) ∧
        MeasurePreserving f (μ : Measure Ω) (μ : Measure Ω) := by sorry
