-- Prove2me | Theorems.Thm_BalanceSpecification_measureEntropy_le_blockEntropy_div
-- name    : BalanceSpecification.measureEntropy_le_blockEntropy_div
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:10:00.719786+00:00
-- url     : https://prove2.me/theorems/4ee60bc0-5f02-4b70-a339-bbdbb4db4b62
-- title:
--   Balance Specification: measure Entropy le block Entropy div
-- statement:
--   The Balance Specification construction uses the measure Entropy le block Entropy div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockEntropy.lean#L266-L269
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockEntropy.lean#L266-L269

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

theorem BalanceSpecification.measureEntropy_le_blockEntropy_div {μ : ProbabilityMeasure X.carrier}
    (hInv : IsInvariant μ) {n : ℕ} (hn : n ≠ 0) :
    measureEntropy μ hInv ≤ blockEntropy μ n / n := by sorry
