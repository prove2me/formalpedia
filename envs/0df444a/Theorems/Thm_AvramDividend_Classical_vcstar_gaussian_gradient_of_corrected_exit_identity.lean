-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_gaussian_gradient_of_corrected_exit_identity
-- name    : AvramDividend.Classical.vcstar_gaussian_gradient_of_corrected_exit_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:48:25.194519+00:00
-- url     : https://prove2.me/theorems/47974566-4113-4029-8fc4-7ff05f325121
-- title:
--   Global Gaussian barrier gradient from the corrected two-sided exit identity
-- statement:
--   For a standing Gaussian spectrally negative Levy process, the corrected killed two-sided exit identity implies that the optimal barrier candidate is differentiable at all strictly positive reserves and has derivative at least one everywhere.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 3 and scale regularity under condition (3.3).

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_gaussian_tilt_monotone_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_scale_C1_tilt

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem vcstar_gaussian_gradient_of_corrected_exit_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (vcstar W) x ∧ 1 ≤ deriv (vcstar W) x := by sorry
end AvramDividend.Classical
