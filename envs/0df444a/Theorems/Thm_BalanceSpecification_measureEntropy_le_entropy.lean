-- Prove2me | Theorems.Thm_BalanceSpecification_measureEntropy_le_entropy
-- name    : BalanceSpecification.measureEntropy_le_entropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:09:26.087429+00:00
-- url     : https://prove2.me/theorems/c19cd54d-67ed-4771-9cd6-36c2f7fe2394
-- title:
--   Balance Specification: measure Entropy le entropy
-- statement:
--   The finite partition inequality gives the entropy bound by the shift's
--   actual topological word-growth entropy.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockEntropy.lean#L290-L295
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockEntropy.lean#L290-L295

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.measureEntropy_le_entropy (hX : X.carrier.Nonempty)
    {μ : ProbabilityMeasure X.carrier} (hInv : IsInvariant μ) :
    measureEntropy μ hInv ≤ entropy X hX := by sorry
