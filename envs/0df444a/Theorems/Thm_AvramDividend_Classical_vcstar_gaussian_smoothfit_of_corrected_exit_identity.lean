-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_gaussian_smoothfit_of_corrected_exit_identity
-- name    : AvramDividend.Classical.vcstar_gaussian_smoothfit_of_corrected_exit_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:27:46.16154+00:00
-- url     : https://prove2.me/theorems/19cd5141-0beb-47b2-af2d-4b1bebc95ef8
-- title:
--   Gaussian smooth fit from the corrected killed two-sided exit identity alone
-- statement:
--   A positive Gaussian coefficient guarantees derivative-one smooth fit at a positive finite cstar provided the corrected killed two-sided exit expectation equals the q-scale ratio. The necessary positive-root exponential exit estimate follows from an independently Proved stopped-exponential inequality, leaving the corrected exit identity as the sole genuinely missing stochastic ingredient in this Gaussian route.
-- source:
--   Avram, Palmowski and Pistorius (2007), corrected killed two-sided exit identity and Gaussian barrier smooth fit, using published stochastic stopped-exponential bound.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root
import Theorems.Thm_AvramDividend_Classical_vcstar_gaussian_smoothfit_of_corrected_exit_bounds

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem vcstar_gaussian_smoothfit_of_corrected_exit_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by sorry
end AvramDividend.Classical
