-- Prove2me | Theorems.Thm_BalanceSpecification_map_finitePointProbability
-- name    : BalanceSpecification.map_finitePointProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:12:33.469892+00:00
-- url     : https://prove2.me/theorems/9062e3b0-5ae2-4b8d-8477-a067c29fa704
-- title:
--   Balance Specification: map finite Point Probability
-- statement:
--   Push-forward commutes with equal finite point averaging.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L95-L103
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L95-L103

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_VariationalPrinciple
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
omit [Fintype A] [DiscreteTopology A] [BorelSpace A]

theorem BalanceSpecification.map_finitePointProbability {I : Type*} [Fintype I] [Nonempty I]
    (x : I → X.carrier) {f : X.carrier → X.carrier} (hf : Measurable f) :
    (finitePointProbability x).map hf.aemeasurable = finitePointProbability (fun i => f (x i)) := by sorry
