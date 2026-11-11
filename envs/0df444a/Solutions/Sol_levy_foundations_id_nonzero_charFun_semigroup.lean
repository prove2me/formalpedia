-- Prove2me | solution 1 for levy_foundations_id_nonzero_charFun_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T08:13:33.8973+00:00
-- url     : https://prove2.me/submissions/f8c6c8a0-0a53-4d83-8414-c1a273ae2945

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Theorems.Thm_levy_foundations_charFun_continuous_log
import Theorems.Thm_levy_foundations_id_log_exp_powers_are_charFun

open MeasureTheory ProbabilityTheory


theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ)
    (hnonzero : ∀ ξ : ℝ, charFun μ ξ ≠ 0) :
    ∃ ψ : ℝ → ℂ,
      Continuous ψ ∧
      (∀ ξ : ℝ, charFun μ ξ = Complex.exp (ψ ξ)) ∧
      (∀ t : ℝ, 0 ≤ t →
        ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
          ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) := by
  obtain ⟨ψ, hcont, hzero, hchar⟩ := levy_foundations_charFun_continuous_log hnonzero
  exact ⟨ψ, hcont, hchar, fun t ht =>
    levy_foundations_id_log_exp_powers_are_charFun hμ ψ hcont hzero hchar t ht⟩
