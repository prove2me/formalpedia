-- Prove2me | Theorems.Thm_BalanceSpecification_isClosed_setOf_isInvariant
-- name    : BalanceSpecification.isClosed_setOf_isInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:11:56.297322+00:00
-- url     : https://prove2.me/theorems/f3dec92d-3e89-4947-894f-6d4255e8af3a
-- title:
--   Balance Specification: is Closed set Of is Invariant
-- statement:
--   Invariant probability measures form a closed subset of all probability measures.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L124-L149
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L124-L149

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
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.isClosed_setOf_isInvariant (X : ShiftSpace A) :
    IsClosed {μ : ProbabilityMeasure X.carrier | IsInvariant μ} := by sorry
