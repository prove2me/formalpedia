-- Prove2me | Theorems.Thm_BalanceSpecification_exists_invariant_probability
-- name    : BalanceSpecification.exists_invariant_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:12:41.857804+00:00
-- url     : https://prove2.me/theorems/3dc503f4-3a6c-4e91-8519-0a8d77c734ad
-- title:
--   Balance Specification: exists invariant probability
-- statement:
--   Every nonempty shift possesses an invariant Borel probability measure.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L152-L159
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L152-L159

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

theorem BalanceSpecification.exists_invariant_probability (hX : X.carrier.Nonempty) :
    ∃ μ : ProbabilityMeasure X.carrier, IsInvariant μ := by sorry
