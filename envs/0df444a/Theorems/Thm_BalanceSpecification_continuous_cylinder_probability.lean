-- Prove2me | Theorems.Thm_BalanceSpecification_continuous_cylinder_probability
-- name    : BalanceSpecification.continuous_cylinder_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:11:47.666319+00:00
-- url     : https://prove2.me/theorems/ec19d2f7-62a7-47bb-a490-5501b239392e
-- title:
--   Balance Specification: continuous cylinder probability
-- statement:
--   Cylinder probabilities depend continuously on the probability measure.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L75-L78
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L75-L78

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

theorem BalanceSpecification.continuous_cylinder_probability (X : ShiftSpace A) (w : Word A) (k : ℤ) :
    Continuous (fun μ : ProbabilityMeasure X.carrier =>
      (μ : Measure X.carrier).real (cylinder X w k)) := by sorry
