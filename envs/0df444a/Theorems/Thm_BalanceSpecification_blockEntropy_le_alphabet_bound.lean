-- Prove2me | Theorems.Thm_BalanceSpecification_blockEntropy_le_alphabet_bound
-- name    : BalanceSpecification.blockEntropy_le_alphabet_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:12:46.608113+00:00
-- url     : https://prove2.me/theorems/69fbbe05-e0c6-4c3f-843c-49a5043a1434
-- title:
--   Balance Specification: block Entropy le alphabet bound
-- statement:
--   Finite block entropy is bounded by length times the alphabet logarithm.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L76-L91
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L76-L91

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

theorem BalanceSpecification.blockEntropy_le_alphabet_bound (hX : X.carrier.Nonempty)
    (μ : ProbabilityMeasure X.carrier) (n : ℕ) :
    blockEntropy μ n ≤ (n : ℝ) * Real.log (Fintype.card A) := by sorry
