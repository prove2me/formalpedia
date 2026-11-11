-- Prove2me | solution 1 for levy_foundations_cnd_exponent_has_triplet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:09:33.669002+00:00
-- url     : https://prove2.me/submissions/e4d6c964-9b9e-4a75-88fd-099b3d0cb8ed

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
import Theorems.Thm_levy_foundations_public_cnd_levyKhintchine_formula

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hzero : ψ 0 = 0)
    (hherm : ∀ ξ : ℝ, ψ (-ξ) = starRingEnd ℂ (ψ ξ))
    (hcnd : ProbabilityTheory.IsConditionallyNegativeDefinite ψ) :
    ∃ T : LevyFoundations.LevyKhintchineTriple,
      ∀ ξ : ℝ, ψ ξ = LevyFoundations.exponent T ξ := by
  obtain ⟨U, hU⟩ :=
    levy_foundations_public_cnd_levyKhintchine_formula hψ hzero hcnd hherm
  let T : LevyFoundations.LevyKhintchineTriple :=
    { drift := U.drift
      gaussianVariance := U.gaussianVariance
      levyMeasure := U.levyMeasure
      levyMeasure_condition := U.levyMeasure_isLevyMeasure }
  refine ⟨T, ?_⟩
  intro ξ
  calc
    ψ ξ = (↑U.drift * ↑ξ * Complex.I
      - ↑(U.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
      + MeasureTheory.integral U.levyMeasure
          (fun x => ProbabilityTheory.levyCompensatedIntegrand ξ x)) := hU ξ
    _ = LevyFoundations.exponent T ξ := by
      have heq :
          (fun x => ProbabilityTheory.levyCompensatedIntegrand ξ x) =
          (fun x => LevyFoundations.compensatedIntegrand ξ x) := by
        funext x
        unfold ProbabilityTheory.levyCompensatedIntegrand
          LevyFoundations.compensatedIntegrand
        ring
      change
        (↑U.drift * ↑ξ * Complex.I
          - ↑(U.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
          + MeasureTheory.integral U.levyMeasure
              (fun x => ProbabilityTheory.levyCompensatedIntegrand ξ x)) =
        (↑U.drift * ↑ξ * Complex.I
          - ↑(U.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
          + MeasureTheory.integral U.levyMeasure
              (fun x => LevyFoundations.compensatedIntegrand ξ x))
      rw [heq]
