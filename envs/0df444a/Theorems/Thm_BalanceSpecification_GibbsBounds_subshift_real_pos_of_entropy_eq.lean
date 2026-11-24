-- Prove2me | Theorems.Thm_BalanceSpecification_GibbsBounds_subshift_real_pos_of_entropy_eq
-- name    : BalanceSpecification.GibbsBounds.subshift_real_pos_of_entropy_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:48.201997+00:00
-- url     : https://prove2.me/theorems/5da110ec-8b15-4e5c-ad24-4fd4583e4ad8
-- title:
--   Gibbs Bounds: subshift real pos of entropy eq
-- statement:
--   Equal entropy forces positive Gibbs probability for the embedded subshift.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L153-L169
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L153-L169

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

theorem BalanceSpecification.GibbsBounds.subshift_real_pos_of_entropy_eq
    {X Y : ShiftSpace A} {hX : X.carrier.Nonempty} (hY : Y.carrier.Nonempty)
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hB : GibbsBounds hX μ K)
    (hμ : IsInvariant μ) (hYX : Y.carrier ⊆ X.carrier)
    (heq : entropy Y hY = entropy X hX) :
    0 < (μ : Measure X.carrier).real {x : X.carrier | x.val ∈ Y.carrier} := by sorry
