-- Prove2me | solution 4 for levy_foundations_characterisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T09:10:59.024742+00:00
-- url     : https://prove2.me/submissions/29167818-e590-44a3-8ec6-1b3e8c018c72

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
import Theorems.Thm_levy_foundations_representation
import Theorems.Thm_levy_foundations_converse

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- Characterisation follows from the M5 forward representation and
the already established Lévy–Khintchine converse. -/
theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    LevyFoundations.isInfinitelyDivisible μ ↔
      ∃ T : LevyFoundations.LevyKhintchineTriple,
        ∀ ξ : ℝ, charFun μ ξ =
          Complex.exp (LevyFoundations.exponent T ξ) := by
  constructor
  · intro hμ
    exact levy_foundations_representation hμ
  · rintro ⟨T, hT⟩
    obtain ⟨ν, hνprob, hνdiv, hνcf⟩ := levy_foundations_converse T
    haveI : IsProbabilityMeasure ν := hνprob
    have hμν : μ = ν := by
      apply Measure.ext_of_charFun
      funext ξ
      rw [hT ξ, hνcf ξ]
    rw [hμν]
    exact hνdiv
