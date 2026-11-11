-- Prove2me | solution 3 for levy_foundations_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:37:05.137231+00:00
-- url     : https://prove2.me/submissions/53967384-fef5-4848-853a-267001194bf9

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
import Theorems.Thm_levy_foundations_representation
import Theorems.Thm_LevyFoundations_leanlevy_chat16_exp_exponent_injective

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ) :
    ∃! T : LevyFoundations.LevyKhintchineTriple,
      ∀ ξ : ℝ, charFun μ ξ =
        Complex.exp (LevyFoundations.exponent T ξ) := by
  obtain ⟨T, hT⟩ := levy_foundations_representation hμ
  refine ⟨T, hT, ?_⟩
  intro U hU
  apply LevyFoundations.leanlevy_chat16_exp_exponent_injective U T
  intro ξ
  calc
    Complex.exp (LevyFoundations.exponent U ξ) = charFun μ ξ := (hU ξ).symm
    _ = Complex.exp (LevyFoundations.exponent T ξ) := hT ξ
