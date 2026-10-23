-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuousOn_locally_integrable_left
-- name    : AvramDividend.Classical.positive_causal_convolution_continuousOn_locally_integrable_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T18:55:49.397176+00:00
-- url     : https://prove2.me/theorems/c2794b16-f139-49d3-a37d-9f07b2d26ed4
-- title:
--   Positive causal convolution is continuous for locally integrable kernels
-- statement:
--   If a real causal kernel is integrable on every bounded positive-time interval and the right factor has a globally continuous zero extension from positive times, their causal convolution is continuous on all strictly positive times. Each x admits a finite cutoff of the left kernel; the resulting globally integrable convolution agrees locally with the original convolution.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuousOn_local_right
open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.positive_causal_convolution_continuousOn_locally_integrable_left
    (f g : ℝ → ℝ)
    (hf : ∀ R : ℝ, 0 < R → IntegrableOn f (Ioc (0 : ℝ) R) volume)
    (hg : Continuous ((Ioi (0 : ℝ)).indicator g)) :
    ContinuousOn
      (MeasureTheory.posConvolution f g (ContinuousLinearMap.mul ℝ ℝ) volume)
      (Ioi (0 : ℝ)) := by sorry
