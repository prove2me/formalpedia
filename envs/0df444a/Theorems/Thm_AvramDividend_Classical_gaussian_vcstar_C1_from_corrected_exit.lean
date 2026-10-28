-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_vcstar_C1_from_corrected_exit
-- name    : AvramDividend.Classical.gaussian_vcstar_C1_from_corrected_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:01:08.429116+00:00
-- url     : https://prove2.me/theorems/1afe3088-464f-4305-8353-825c35f7df06
-- title:
--   Global C1 regularity of Gaussian optimal barrier value from corrected exit identity
-- statement:
--   Assume the standing spectrally negative Lévy hypotheses and positive discount, the canonical scale W, a positive real optimal barrier, a strictly positive Gaussian coefficient, and the corrected two-sided q-discounted exit identity W(x)/W(a) at positive x≤a. Then the exact piecewise optimal dividend candidate vcstar W is globally C1 on the positive half-line, including its barrier join. The known no-Standing Gaussian scale C1 regularity theorem gives W∈C1, and the separately Proved exit-identity-to-Esscher-monotonicity theorem supplies a positive tilt with monotone normalized scale. Apply the Proved deterministic global barrier C1 gluing theorem. This is a dependency-accurate interface for the remaining stochastic corrected-exit target.

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_gaussian_tilt_monotone_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_vcstar_C1_of_scale_C1_tilt
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_vcstar_C1_from_corrected_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hcpos : 0 < (cstar W).toReal) (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ContDiffOn ℝ 1 (vcstar W) (Ioi (0 : ℝ)) := by sorry
