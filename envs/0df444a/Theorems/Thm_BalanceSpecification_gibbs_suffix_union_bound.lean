-- Prove2me | Theorems.Thm_BalanceSpecification_gibbs_suffix_union_bound
-- name    : BalanceSpecification.gibbs_suffix_union_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:15:09.108721+00:00
-- url     : https://prove2.me/theorems/2e0b7c22-44e4-4624-bc10-a9704f5be716
-- title:
--   Balance Specification: gibbs suffix union bound
-- statement:
--   Summing the upper quasi-Bernoulli bound over right adjacent cylinders.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsErgodic.lean#L161-L200
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsErgodic.lean#L161-L200

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

theorem BalanceSpecification.gibbs_suffix_union_bound {X : ShiftSpace A} {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} (hμ : IsInvariant μ) {K : ℝ}
    (hG : GibbsBounds hX μ K) (S : Finset (Word A)) {l : ℕ}
    (hS : ∀ a ∈ S, a.length = l) (k : ℤ) (v w : Word A) :
    (μ : Measure X.carrier).real
        (cylinder X (v ++ w) k ∩
          (⋃ a ∈ S, cylinder X a (k + (v ++ w).length))) ≤
      K ^ 3 * (μ : Measure X.carrier).real (cylinder X v 0) *
        (μ : Measure X.carrier).real
          (cylinder X w (k + v.length) ∩
            (⋃ a ∈ S, cylinder X a (k + (v ++ w).length))) := by sorry
