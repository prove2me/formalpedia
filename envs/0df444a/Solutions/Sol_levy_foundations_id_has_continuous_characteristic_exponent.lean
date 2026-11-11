-- Prove2me | solution 1 for levy_foundations_id_has_continuous_characteristic_exponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:58:10.979909+00:00
-- url     : https://prove2.me/submissions/4ef06f46-b492-4a8a-a278-d052aa26c6ae

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Theorems.Thm_levy_foundations_id_charFun_ne_zero
import Theorems.Thm_levy_foundations_id_nonzero_charFun_semigroup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ) :
    ∃ ψ : ℝ → ℂ,
      Continuous ψ ∧
      (∀ ξ : ℝ, charFun μ ξ = Complex.exp (ψ ξ)) ∧
      (∀ t : ℝ, 0 ≤ t →
        ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
          ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) := by
  have hnonzero : ∀ ξ : ℝ, charFun μ ξ ≠ 0 :=
    levy_foundations_id_charFun_ne_zero hμ
  exact levy_foundations_id_nonzero_charFun_semigroup hμ hnonzero
