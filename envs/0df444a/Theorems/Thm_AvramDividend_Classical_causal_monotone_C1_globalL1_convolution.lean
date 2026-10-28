-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_monotone_C1_globalL1_convolution
-- name    : AvramDividend.Classical.causal_monotone_C1_globalL1_convolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:42:22.974821+00:00
-- url     : https://prove2.me/theorems/8a549c3a-219d-4339-a72d-962761033974
-- title:
--   C1 of causal monotone-kernel convolution under global L1 input and derivative assumptions
-- statement:
--   For a continuous L1 positive-time input and a monotone C1 positive-time kernel vanishing at zero, with globally L1 ordinary derivative, their causal convolution is C1 on the positive half-line. This combines the already Proved zero-origin derivative primitive, L1 convolution smoothing and time-reversal theorems. It supplies an exact locally reusable intermediate for the unqualified monotone convolution theorem, with the remaining work being compact-horizon localisation rather than calculus.
-- source:
--   Proved monotone_C1_kernel_derivative_primitive_from_zero (b928d68e-c31a-4b0f-93aa-00d860096458), causal_l1_convolution_C1_of_kernel_primitive (26e95536-54ba-4c2e-afee-6a23f1b3933e), causal_convolution_time_reversal (f1622c94-540f-40cd-980d-3b1132ca67c4). Open canonical causal_convolution_contDiffOn_one_of_monotone_C1_kernel (df538b19-3214-472b-a34c-c964a375643e).

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_monotone_C1_kernel_derivative_primitive_from_zero
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_C1_of_kernel_primitive
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal
open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.causal_monotone_C1_globalL1_convolution
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hfL1 : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hg0 : g 0 = 0)
    (hgmono : MonotoneOn g (Ici (0 : ℝ)))
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ)))
    (hgderivL1 : IntegrableOn (deriv g) (Ioi (0 : ℝ)) volume) :
    ContDiffOn ℝ 1
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        f s * g (x - s) ∂volume) (Ioi (0 : ℝ)) := by sorry
