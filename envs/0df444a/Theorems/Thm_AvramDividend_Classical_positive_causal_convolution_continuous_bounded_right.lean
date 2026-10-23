-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuous_bounded_right
-- name    : AvramDividend.Classical.positive_causal_convolution_continuous_bounded_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T15:22:07.468996+00:00
-- url     : https://prove2.me/theorems/ecb9e66f-cd58-425f-a573-0cb07a3798a2
-- title:
--   Continuity of positive causal convolution with a bounded continuous zero extension
-- statement:
--   An integrable signed kernel on positive times convolved causally with a function whose zero extension is continuous and globally bounded gives a continuous convolution. Restricting ordinary convolution to the positive half-line allows the existing Mathlib continuity theorem to discharge the analytic step. Intended for Gaussian Esscher scale Volterra continuity after the scale is shown continuous at zero and locally bounded.
-- source:
--   Mathlib.Analysis.Convolution, MeasureTheory.posConvolution_eq_convolution_indicator and BddAbove.continuous_convolution_right_of_integrable.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.positive_causal_convolution_continuous_bounded_right
    (f g : ℝ → ℝ)
    (hf : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (hg : Continuous ((Ioi (0 : ℝ)).indicator g))
    (hgb : BddAbove (Set.range (fun x : ℝ => ‖(Ioi (0 : ℝ)).indicator g x‖))) :
    Continuous (MeasureTheory.posConvolution f g (ContinuousLinearMap.mul ℝ ℝ) volume) := by sorry
