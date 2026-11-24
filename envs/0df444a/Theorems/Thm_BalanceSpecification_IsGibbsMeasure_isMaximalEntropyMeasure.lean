-- Prove2me | Theorems.Thm_BalanceSpecification_IsGibbsMeasure_isMaximalEntropyMeasure
-- name    : BalanceSpecification.IsGibbsMeasure.isMaximalEntropyMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:10:11.468393+00:00
-- url     : https://prove2.me/theorems/56b45603-1142-4e4f-978e-a52d383512fe
-- title:
--   Is Gibbs Measure: is Maximal Entropy Measure
-- statement:
--   Every invariant Gibbs measure is a measure of maximal entropy.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MaximalEntropy.lean#L72-L76
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MaximalEntropy.lean#L72-L76

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

theorem BalanceSpecification.IsGibbsMeasure.isMaximalEntropyMeasure {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} (hG : IsGibbsMeasure hX μ) :
    IsMaximalEntropyMeasure hX μ := by sorry
