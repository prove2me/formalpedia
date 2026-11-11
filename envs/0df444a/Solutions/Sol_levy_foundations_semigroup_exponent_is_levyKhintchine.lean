-- Prove2me | solution 1 for levy_foundations_semigroup_exponent_is_levyKhintchine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:18:19.535959+00:00
-- url     : https://prove2.me/submissions/b9bba6b5-a33d-46fd-bacf-f9b328de2b4d

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
import Theorems.Thm_levy_foundations_semigroup_exponent_is_cnd
import Theorems.Thm_levy_foundations_cnd_exponent_has_triplet

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- The Lévy–Khintchine representation follows from the Schoenberg
characterisation and the conditional-negative-definite representation. -/
theorem solution
    (ψ : ℝ → ℂ)
    (hψ : Continuous ψ)
    (hsemigroup :
      ∀ t : ℝ, 0 ≤ t →
        ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
          ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) :
    ∃ T : LevyFoundations.LevyKhintchineTriple,
      ∀ ξ : ℝ, ψ ξ = LevyFoundations.exponent T ξ := by
  obtain ⟨hzero, hherm, hcnd⟩ :=
    levy_foundations_semigroup_exponent_is_cnd ψ hψ hsemigroup
  exact levy_foundations_cnd_exponent_has_triplet ψ hψ hzero hherm hcnd
