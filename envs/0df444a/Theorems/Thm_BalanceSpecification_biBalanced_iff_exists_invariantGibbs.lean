-- Prove2me | Theorems.Thm_BalanceSpecification_biBalanced_iff_exists_invariantGibbs
-- name    : BalanceSpecification.biBalanced_iff_exists_invariantGibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:15:14.042648+00:00
-- url     : https://prove2.me/theorems/ec2817e3-97d4-4214-8bb4-bce02c530e71
-- title:
--   Balance Specification: bi Balanced iff exists invariant Gibbs
-- statement:
--   The complete cited invariant-Gibbs characterization, proved in both directions.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsBalance.lean#L151-L153
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsBalance.lean#L151-L153

module
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsBalance
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.biBalanced_iff_exists_invariantGibbs (hX : X.carrier.Nonempty) :
    BiBalanced (language X) ↔ ∃ μ : ProbabilityMeasure X.carrier, IsGibbsMeasure hX μ := by sorry
