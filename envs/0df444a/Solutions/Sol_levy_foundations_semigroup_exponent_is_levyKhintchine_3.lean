-- Prove2me | solution 3 for levy_foundations_semigroup_exponent_is_levyKhintchine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T11:26:13.80353+00:00
-- url     : https://prove2.me/submissions/9b3ad3fb-72ed-4db3-a854-7edf7f781bfb

import Theorems.Thm_levy_foundations_semigroup_exponent_is_cnd
import Theorems.Thm_levy_foundations_cnd_exponent_has_triplet

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- A characteristic exponential semigroup gives the standard triplet
once its infinitesimal generator has been shown conditionally negative. -/
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
