-- Prove2me | Theorems.Thm_BalanceSpecification_upperSemicontinuous_measureEntropy
-- name    : BalanceSpecification.upperSemicontinuous_measureEntropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:11:52.277965+00:00
-- url     : https://prove2.me/theorems/2eb7b2e3-28f0-404e-a9ac-ce7a6132fddb
-- title:
--   Balance Specification: upper Semicontinuous measure Entropy
-- statement:
--   On the actual invariant-measure subtype, measure entropy is upper semicontinuous.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L104-L121
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L104-L121

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

theorem BalanceSpecification.upperSemicontinuous_measureEntropy :
    UpperSemicontinuous (fun μ : {μ : ProbabilityMeasure X.carrier // IsInvariant μ} =>
      measureEntropy μ.val μ.property) := by sorry
