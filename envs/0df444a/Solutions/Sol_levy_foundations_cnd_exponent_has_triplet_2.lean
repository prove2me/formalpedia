-- Prove2me | solution 2 for levy_foundations_cnd_exponent_has_triplet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T11:25:38.747223+00:00
-- url     : https://prove2.me/submissions/1791ab18-83ba-4f1e-93c9-2264b8aa6191

import Theorems.Thm_levy_foundations_public_cnd_levyKhintchine_formula
import Theorems.Thm_levy_foundations_leanlevy_triplet_conversion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- Transport the analytic Lévy–Khintchine formula into the Foundations
triplet convention using the previously verified formula conversion. -/
theorem solution
    (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hzero : ψ 0 = 0)
    (hherm : ∀ ξ : ℝ, ψ (-ξ) = starRingEnd ℂ (ψ ξ))
    (hcnd : ProbabilityTheory.IsConditionallyNegativeDefinite ψ) :
    ∃ T : LevyFoundations.LevyKhintchineTriple,
      ∀ ξ : ℝ, ψ ξ = LevyFoundations.exponent T ξ := by
  obtain ⟨T, hT⟩ :=
    levy_foundations_public_cnd_levyKhintchine_formula hψ hzero hcnd hherm
  obtain ⟨U, hU⟩ := levy_foundations_leanlevy_triplet_conversion T
  exact ⟨U, fun ξ => (hT ξ).trans (hU ξ)⟩
