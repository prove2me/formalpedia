-- Prove2me | Theorems.Thm_BalanceSpecification_blockEntropy_translated_add_le
-- name    : BalanceSpecification.blockEntropy_translated_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:12:37.243009+00:00
-- url     : https://prove2.me/theorems/eb405539-b85c-4b08-b10b-79e32165f85b
-- title:
--   Balance Specification: block Entropy translated add le
-- statement:
--   The Balance Specification construction uses the block Entropy translated add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L68-L73
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L68-L73

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

theorem BalanceSpecification.blockEntropy_translated_add_le (μ : ProbabilityMeasure X.carrier) (s m n : ℕ) :
    blockEntropy (translatedProbability μ s) (m + n) ≤
      blockEntropy (translatedProbability μ s) m +
        blockEntropy (translatedProbability μ (s + m)) n := by sorry
