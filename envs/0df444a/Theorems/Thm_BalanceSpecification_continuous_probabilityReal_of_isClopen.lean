-- Prove2me | Theorems.Thm_BalanceSpecification_continuous_probabilityReal_of_isClopen
-- name    : BalanceSpecification.continuous_probabilityReal_of_isClopen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:11:09.600888+00:00
-- url     : https://prove2.me/theorems/6f906ccd-0065-4b23-8209-692f2856116e
-- title:
--   Balance Specification: continuous probability Real of is Clopen
-- statement:
--   Weak convergence makes the real probability of a clopen set continuous.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L23-L34
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L23-L34

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology

theorem BalanceSpecification.continuous_probabilityReal_of_isClopen
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω] {E : Set Ω} (hE : IsClopen E) :
    Continuous (fun μ : ProbabilityMeasure Ω => (μ : Measure Ω).real E) := by sorry
