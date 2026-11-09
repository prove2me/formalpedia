-- Prove2me | solution 2 for levy_foundations_characterisation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:22:39.535567+00:00
-- url     : https://prove2.me/submissions/348338c6-3eae-42da-b423-71495792651d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
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
