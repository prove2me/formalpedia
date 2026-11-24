-- Prove2me | Theorems.Thm_BalanceSpecification_GibbsBounds_one_le
-- name    : BalanceSpecification.GibbsBounds.one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:32.081146+00:00
-- url     : https://prove2.me/theorems/51791f11-90eb-49c5-9526-8175d6dc7b4c
-- title:
--   Gibbs Bounds: one le
-- statement:
--   Every Gibbs constant is at least one, by applying its bound to the empty word.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L139-L143
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean#L139-L143

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Measures
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
omit [DiscreteTopology A] [BorelSpace A]

theorem BalanceSpecification.GibbsBounds.one_le {X : ShiftSpace A} {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hB : GibbsBounds hX μ K) : 1 ≤ K := by sorry
