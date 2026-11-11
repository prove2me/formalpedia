-- Prove2me | solution 1 for levy_foundations_semigroup_exponent_is_cnd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:33:13.437236+00:00
-- url     : https://prove2.me/submissions/46bcbac1-9ee9-416a-bdd4-9d77f8394f1f

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_semigroup_exponent_normalised_hermitian
import Theorems.Thm_levy_foundations_semigroup_exponent_conditionally_negative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- Separate the semigroup generator's normalisation, symmetry and CND estimate. -/
theorem solution
    (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hsemigroup : ∀ t : ℝ, 0 ≤ t →
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) :
    ψ 0 = 0 ∧
      (∀ ξ : ℝ, ψ (-ξ) = starRingEnd ℂ (ψ ξ)) ∧
      ProbabilityTheory.IsConditionallyNegativeDefinite ψ := by
  obtain ⟨hzero, hherm⟩ :=
    levy_foundations_semigroup_exponent_normalised_hermitian ψ hψ hsemigroup
  refine ⟨hzero, hherm, ?_⟩
  exact levy_foundations_semigroup_exponent_conditionally_negative
    ψ hψ hsemigroup
