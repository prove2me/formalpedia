-- Prove2me | Theorems.Thm_BalanceSpecification_exists_maximalEntropyMeasure_of_biBalanced
-- name    : BalanceSpecification.exists_maximalEntropyMeasure_of_biBalanced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:13:47.756864+00:00
-- url     : https://prove2.me/theorems/549a9480-b2c7-4f78-a70a-72862f42354b
-- title:
--   Balance Specification: exists maximal Entropy Measure of bi Balanced
-- statement:
--   Bi-balanced shifts possess an actual measure of maximal entropy.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MaximalEntropy.lean#L79-L83
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MaximalEntropy.lean#L79-L83

module
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.exists_maximalEntropyMeasure_of_biBalanced (hX : X.carrier.Nonempty)
    (hB : BiBalanced (language X)) :
    ∃ μ : ProbabilityMeasure X.carrier, IsMaximalEntropyMeasure hX μ := by sorry
