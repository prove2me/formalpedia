-- Prove2me | solution 1 for levy_foundations_compoundPoissonCharFunEqTripleExponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:13:30.543406+00:00
-- url     : https://prove2.me/submissions/ad6d0dd0-553c-438d-b8c2-6a92e6e56dd3

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isLevyMeasure
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
import Theorems.Thm_levy_foundations_compoundPoissonCharFun
import Theorems.Thm_levy_foundations_compoundPoissonTripleExponentIdentity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν']
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) (b : ℝ) (t : ℝ≥0)
    (hlevy : LevyFoundations.isLevyMeasure ((r : ℝ≥0∞) • ν'))
    (ξ : ℝ) :
    charFun (μ.map (LevyFoundations.compoundPoisson b τ Y (t : ℝ))) ξ =
      Complex.exp ((t : ℝ) * LevyFoundations.exponent
        (LevyFoundations.compoundPoissonTripleGivenLevyMeasure b r ν' hlevy) ξ) := by
  rw [levy_foundations_compoundPoissonTripleExponentIdentity b r ν' hlevy ξ]
  exact levy_foundations_compoundPoissonCharFun hd hr b t ξ
