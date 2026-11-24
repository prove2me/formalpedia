-- Prove2me | Theorems.Thm_BalanceSpecification_exists_maximalEntropyMeasure
-- name    : BalanceSpecification.exists_maximalEntropyMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:13:00.545394+00:00
-- url     : https://prove2.me/theorems/f05d008b-a249-4d77-9ed7-920b5087a901
-- title:
--   Balance Specification: exists maximal Entropy Measure
-- statement:
--   Every nonempty finite-alphabet shift possesses a measure of maximal entropy.
--   The measure is constructed as a weak cluster point of uniform long-word orbit averages.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L211-L249
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L211-L249

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

theorem BalanceSpecification.exists_maximalEntropyMeasure (hX : X.carrier.Nonempty) :
    ∃ μ : ProbabilityMeasure X.carrier, IsMaximalEntropyMeasure hX μ := by sorry
