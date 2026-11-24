-- Prove2me | Theorems.Thm_BalanceSpecification_GibbsBounds_subshiftCylinderEvent_lower_of_entropy_eq
-- name    : BalanceSpecification.GibbsBounds.subshiftCylinderEvent_lower_of_entropy_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:36.053242+00:00
-- url     : https://prove2.me/theorems/4cf36ed5-e063-4170-a2a4-11742309f22f
-- title:
--   Gibbs Bounds: subshift Cylinder Event lower of entropy eq
-- statement:
--   Under equal entropies, every centered approximation to a nonempty subshift
--   has probability at least `1/K`, as in the source proof.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L115-L150
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean#L115-L150

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

theorem BalanceSpecification.GibbsBounds.subshiftCylinderEvent_lower_of_entropy_eq
    {X Y : ShiftSpace A} {hX : X.carrier.Nonempty} (hY : Y.carrier.Nonempty)
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hB : GibbsBounds hX μ K)
    (hμ : IsInvariant μ) (hYX : Y.carrier ⊆ X.carrier)
    (heq : entropy Y hY = entropy X hX) (n : ℕ) :
    1 / K ≤ (μ : Measure X.carrier).real (subshiftCylinderEvent X Y n) := by sorry
