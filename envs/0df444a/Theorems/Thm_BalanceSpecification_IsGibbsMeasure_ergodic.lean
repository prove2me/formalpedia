-- Prove2me | Theorems.Thm_BalanceSpecification_IsGibbsMeasure_ergodic
-- name    : BalanceSpecification.IsGibbsMeasure.ergodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:11.732343+00:00
-- url     : https://prove2.me/theorems/e4e15533-9408-4252-b4b7-5458e3193b6b
-- title:
--   Is Gibbs Measure: ergodic
-- statement:
--   Every invariant Gibbs measure on an irreducible shift is ergodic.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsErgodic.lean#L365-L428
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsErgodic.lean#L365-L428

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [Fintype A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A]

theorem BalanceSpecification.IsGibbsMeasure.ergodic {X : ShiftSpace A} {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} (hG : IsGibbsMeasure hX μ)
    (hirr : Irreducible X) : Ergodic (shiftMap X) (μ : Measure X.carrier) := by sorry
