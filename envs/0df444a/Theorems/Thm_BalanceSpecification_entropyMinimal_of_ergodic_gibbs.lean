-- Prove2me | Theorems.Thm_BalanceSpecification_entropyMinimal_of_ergodic_gibbs
-- name    : BalanceSpecification.entropyMinimal_of_ergodic_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:14:51.996657+00:00
-- url     : https://prove2.me/theorems/7af219b8-4977-43e5-bb53-d0215cc843db
-- title:
--   Balance Specification: entropy Minimal of ergodic gibbs
-- statement:
--   The complete source lemma: an ergodic Gibbs measure makes its shift entropy
--   minimal, with the empty proper subshift included through extended entropy.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L225-L231
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L225-L231

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A]
variable [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]

theorem BalanceSpecification.entropyMinimal_of_ergodic_gibbs
    {X : ShiftSpace A} (hX : X.carrier.Nonempty)
    {μ : ProbabilityMeasure X.carrier} (hG : IsGibbsMeasure hX μ)
    (hErg : Ergodic (shiftMap X) (μ : Measure X.carrier)) : EntropyMinimal X := by sorry
