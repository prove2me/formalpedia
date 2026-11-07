-- Prove2me | solution 1 for levy_foundations_characterisation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:27:44.62129+00:00
-- url     : https://prove2.me/submissions/dc864dcb-d837-43fb-a169-7e152f49d8f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
  · rintro ⟨T, hchar⟩
    obtain ⟨μ', hprob, hdiv, hchar'⟩ := levy_foundations_converse T
    haveI : IsProbabilityMeasure μ' := hprob
    have heq : μ = μ' := by
      apply Measure.ext_of_charFun
      funext ξ
      rw [hchar ξ, hchar' ξ]
    rw [heq]
    exact hdiv
