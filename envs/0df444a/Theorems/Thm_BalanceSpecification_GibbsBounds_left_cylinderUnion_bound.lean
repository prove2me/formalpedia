-- Prove2me | Theorems.Thm_BalanceSpecification_GibbsBounds_left_cylinderUnion_bound
-- name    : BalanceSpecification.GibbsBounds.left_cylinderUnion_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:59.039808+00:00
-- url     : https://prove2.me/theorems/fdf59f52-432e-42cc-b9c0-77fa9a7d4f33
-- title:
--   Gibbs Bounds: left cylinder Union bound
-- statement:
--   Summing the upper quasi-Bernoulli bound over left adjacent cylinders.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsErgodic.lean#L66-L92
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsErgodic.lean#L66-L92

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

theorem BalanceSpecification.GibbsBounds.left_cylinderUnion_bound {X : ShiftSpace A}
    {hX : X.carrier.Nonempty} {μ : ProbabilityMeasure X.carrier} {K : ℝ}
    (hB : GibbsBounds hX μ K) (hμ : IsInvariant μ)
    (S : Finset (Word A)) (l : ℕ) (hlen : ∀ a ∈ S, a.length = l)
    (k : ℤ) (v w : Word A) :
    (μ : Measure X.carrier).real
        ((⋃ a ∈ S, cylinder X a k) ∩ cylinder X (v ++ w) (k + l)) ≤
      K ^ 3 * (μ : Measure X.carrier).real
        ((⋃ a ∈ S, cylinder X a k) ∩ cylinder X v (k + l)) *
        (μ : Measure X.carrier).real (cylinder X w 0) := by sorry
