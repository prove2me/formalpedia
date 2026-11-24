-- Prove2me | Theorems.Thm_BalanceSpecification_biBalanced_of_isGibbsMeasure
-- name    : BalanceSpecification.biBalanced_of_isGibbsMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:12:06.270933+00:00
-- url     : https://prove2.me/theorems/921711e3-3418-42bd-ac02-0fb9f91312f7
-- title:
--   Balance Specification: bi Balanced of is Gibbs Measure
-- statement:
--   An invariant Gibbs probability measure supplies both uniform balancedness constants.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsBalance.lean#L117-L148
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsBalance.lean#L117-L148

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

theorem BalanceSpecification.biBalanced_of_isGibbsMeasure {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} (hG : IsGibbsMeasure hX μ) :
    BiBalanced (language X) := by sorry
