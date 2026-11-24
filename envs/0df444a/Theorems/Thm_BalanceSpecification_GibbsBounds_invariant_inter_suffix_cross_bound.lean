-- Prove2me | Theorems.Thm_BalanceSpecification_GibbsBounds_invariant_inter_suffix_cross_bound
-- name    : BalanceSpecification.GibbsBounds.invariant_inter_suffix_cross_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:15:26.271089+00:00
-- url     : https://prove2.me/theorems/56fffd8b-1050-4323-83b1-60b6c0f26ff8
-- title:
--   Gibbs Bounds: invariant inter suffix cross bound
-- statement:
--   Cross-multiplied conditional suffix bound.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsErgodic.lean#L336-L362
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsErgodic.lean#L336-L362

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

theorem BalanceSpecification.GibbsBounds.invariant_inter_suffix_cross_bound {X : ShiftSpace A}
    {hX : X.carrier.Nonempty} {μ : ProbabilityMeasure X.carrier} {K : ℝ}
    (hG : GibbsBounds hX μ K) (hμ : IsInvariant μ)
    {B : Set X.carrier} (hB : MeasurableSet B) (hBinv : (shiftMap X) ⁻¹' B = B)
    {v w : Word A} (hvw : v ++ w ∈ language X) :
    (μ : Measure X.carrier).real (B ∩ cylinder X (v ++ w) 0) *
        (μ : Measure X.carrier).real (cylinder X w 0) ≤
      K ^ 6 * (μ : Measure X.carrier).real (B ∩ cylinder X w 0) *
        (μ : Measure X.carrier).real (cylinder X (v ++ w) 0) := by sorry
