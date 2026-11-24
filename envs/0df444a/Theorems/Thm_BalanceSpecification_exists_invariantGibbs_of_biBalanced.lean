-- Prove2me | Theorems.Thm_BalanceSpecification_exists_invariantGibbs_of_biBalanced
-- name    : BalanceSpecification.exists_invariantGibbs_of_biBalanced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:40:22.567051+00:00
-- url     : https://prove2.me/theorems/c52edd8e-8897-4217-8165-e8b61f1bae4e
-- title:
--   Balance Specification: exists invariant Gibbs of bi Balanced
-- statement:
--   Every nonempty finite-alphabet bi-balanced shift admits an invariant Gibbs
--   probability measure. Both balancedness constants and every exponential estimate
--   used in the construction are derived inside the proof.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L445-L510
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L445-L510

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology ENNReal Classical BoundedContinuousFunction

theorem BalanceSpecification.exists_invariantGibbs_of_biBalanced
    {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
    (hX : X.carrier.Nonempty) (hB : BiBalanced (language X)) :
    ∃ μ : ProbabilityMeasure X.carrier, IsGibbsMeasure hX μ := by sorry
