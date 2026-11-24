-- Prove2me | Theorems.Thm_BalanceSpecification_entropy_lt_of_proper_subshift_of_ergodic_gibbs
-- name    : BalanceSpecification.entropy_lt_of_proper_subshift_of_ergodic_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:14:46.689804+00:00
-- url     : https://prove2.me/theorems/555d6657-0305-4099-a43a-90d37c313d59
-- title:
--   Balance Specification: entropy lt of proper subshift of ergodic gibbs
-- statement:
--   The source's ergodic-Gibbs entropy-minimality lemma, for every nonempty
--   proper subshift. The empty-subshift entropy is handled in the extended-real API.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L173-L221
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L173-L221

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

theorem BalanceSpecification.entropy_lt_of_proper_subshift_of_ergodic_gibbs
    {X : ShiftSpace A} (hX : X.carrier.Nonempty)
    {μ : ProbabilityMeasure X.carrier} (hG : IsGibbsMeasure hX μ)
    (hErg : Ergodic (shiftMap X) (μ : Measure X.carrier))
    {Y : ShiftSpace A} (hY : Y.carrier.Nonempty) (hproper : Y.carrier ⊂ X.carrier) :
    entropy Y hY < entropy X hX := by sorry
