-- Prove2me | solution 2 for levy_foundations_id_has_continuous_characteristic_exponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:02:27.961196+00:00
-- url     : https://prove2.me/submissions/bebb438d-5448-46a5-a2de-f43cef71f00f

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Theorems.Thm_levy_foundations_id_charFun_nonzero
import Theorems.Thm_levy_foundations_charFun_continuous_log
import Theorems.Thm_levy_foundations_id_log_exp_powers_are_charFun

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- Factor the continuous characteristic exponent into nonvanishing,
continuous logarithm and positive-time convolution powers. -/
theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ) :
    ∃ ψ : ℝ → ℂ,
      Continuous ψ ∧
      (∀ ξ : ℝ, charFun μ ξ = Complex.exp (ψ ξ)) ∧
      (∀ t : ℝ, 0 ≤ t →
        ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
          ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) := by
  have hne := levy_foundations_id_charFun_nonzero hμ
  obtain ⟨ψ, hcont, hzero, hchar⟩ :=
    levy_foundations_charFun_continuous_log hne
  refine ⟨ψ, hcont, hchar, ?_⟩
  exact levy_foundations_id_log_exp_powers_are_charFun
    hμ ψ hcont hzero hchar
