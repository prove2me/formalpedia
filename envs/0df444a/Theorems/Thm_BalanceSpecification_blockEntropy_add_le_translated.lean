-- Prove2me | Theorems.Thm_BalanceSpecification_blockEntropy_add_le_translated
-- name    : BalanceSpecification.blockEntropy_add_le_translated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:12:38.786071+00:00
-- url     : https://prove2.me/theorems/6c0eab89-fa1f-4977-ba5e-4eb0b95eba12
-- title:
--   Balance Specification: block Entropy add le translated
-- statement:
--   Finite block entropy splits across an adjacent boundary without an
--   invariance assumption; the second term is evaluated at the translated measure.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L48-L66
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L48-L66

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

theorem BalanceSpecification.blockEntropy_add_le_translated (μ : ProbabilityMeasure X.carrier) (m n : ℕ) :
    blockEntropy μ (m + n) ≤ blockEntropy μ m + blockEntropy (translatedProbability μ m) n := by sorry
