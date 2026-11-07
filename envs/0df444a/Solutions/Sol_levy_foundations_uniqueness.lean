-- Prove2me | solution 1 for levy_foundations_uniqueness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:36:47.670195+00:00
-- url     : https://prove2.me/submissions/65eb9a2d-8f7f-4de8-9bf8-9c70c5377553
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
  apply LevyFoundations.leanlevy_chat16_exp_exponent_injective
  intro ξ
  calc
    Complex.exp (LevyFoundations.exponent U ξ) = charFun μ ξ :=
      (hU ξ).symm
    _ = Complex.exp (LevyFoundations.exponent T ξ) := hT ξ
