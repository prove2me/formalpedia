-- Prove2me | Theorems.Thm_BalanceSpecification_cylinderUnion_log_inverse_le_of_divergence_bound
-- name    : BalanceSpecification.cylinderUnion_log_inverse_le_of_divergence_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:10:32.704223+00:00
-- url     : https://prove2.me/theorems/4dd98bde-3244-425e-a503-8186a16c062d
-- title:
--   Balance Specification: cylinder Union log inverse le of divergence bound
-- statement:
--   The finite KL inequality transferred to a union of admissible equal-length
--   centered cylinders of actual invariant measures.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/AbsoluteContinuity.lean#L94-L133
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/AbsoluteContinuity.lean#L94-L133

module
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_AbsoluteContinuity
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Set Filter
open scoped Topology symmDiff
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.cylinderUnion_log_inverse_le_of_divergence_bound
    {hX : X.carrier.Nonempty} {μ ν : ProbabilityMeasure X.carrier}
    (hG : IsGibbsMeasure hX μ) (hν : IsInvariant ν) {C : ℝ}
    (hD : ∀ n : ℕ, FiniteEntropy.divergence
      (blockDistribution ν (2 * n + 1)) (blockDistribution μ (2 * n + 1)) ≤ C)
    (n : ℕ) (S : Finset (Word A))
    (hS : ∀ w ∈ S, w ∈ language X ∧ w.length = 2 * n + 1)
    (hpos : 0 < (μ : Measure X.carrier).real (⋃ w ∈ S, cylinder X w (-(n : ℤ)))) :
    (ν : Measure X.carrier).real (⋃ w ∈ S, cylinder X w (-(n : ℤ))) *
        Real.log (1 / (μ : Measure X.carrier).real
          (⋃ w ∈ S, cylinder X w (-(n : ℤ)))) ≤ C + Real.log 2 := by sorry
