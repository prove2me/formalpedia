-- Prove2me | solution 1 for levy_foundations_leanlevy_triplet_conversion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:32:24.355194+00:00
-- url     : https://prove2.me/submissions/1a3aabc7-889f-43df-998b-29898935ad5b

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- Translate the LeanLevy triplet into the Foundations triplet. -/
theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple) :
    ∃ U : LevyFoundations.LevyKhintchineTriple,
      ∀ ξ : ℝ,
        (↑T.drift * ↑ξ * Complex.I
          - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
          + MeasureTheory.integral T.levyMeasure
              (fun x => ProbabilityTheory.levyCompensatedIntegrand ξ x))
          = LevyFoundations.exponent U ξ := by
  let U : LevyFoundations.LevyKhintchineTriple :=
    { drift := T.drift
      gaussianVariance := T.gaussianVariance
      levyMeasure := T.levyMeasure
      levyMeasure_condition := by
        exact T.levyMeasure_isLevyMeasure }
  refine ⟨U, ?_⟩
  intro ξ
  have heq :
      (fun x => ProbabilityTheory.levyCompensatedIntegrand ξ x) =
      (fun x => LevyFoundations.compensatedIntegrand ξ x) := by
    funext x
    unfold ProbabilityTheory.levyCompensatedIntegrand
      LevyFoundations.compensatedIntegrand
    ring
  change
    (↑T.drift * ↑ξ * Complex.I
      - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
      + MeasureTheory.integral T.levyMeasure
          (fun x => ProbabilityTheory.levyCompensatedIntegrand ξ x))
    = (↑T.drift * ↑ξ * Complex.I
      - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
      + MeasureTheory.integral T.levyMeasure
          (fun x => LevyFoundations.compensatedIntegrand ξ x))
  rw [heq]
