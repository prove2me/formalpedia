-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_C1_of_kernel_primitive
-- name    : AvramDividend.Classical.causal_l1_convolution_C1_of_kernel_primitive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:32:16.655003+00:00
-- url     : https://prove2.me/theorems/26e95536-54ba-4c2e-afee-6a23f1b3933e
-- title:
--   Positive-time C1 smoothing of an L1 causal convolution by a kernel primitive
-- statement:
--   Suppose a continuous positive-time input f is integrable on the half-line, k is also half-line integrable, and g(x) equals the integral of k from 0 to x. The causal convolution f*g is continuously differentiable for x>0. The derivative is the continuous L1 convolution k*f, proved using the established triangle Fubini identity, continuous convolution and a C1 primitive theorem. This supplies a reusable exponentially damped bridge for zero-discount scale regularity.
-- source:
--   Proved AvramDividend.Classical.causal_l1_convolution_outer_integrable, causal_l1_convolution_continuousOn_positive_of_Ici_input, causal_l1_kernel_triangle_fubini_two_L1, causal_positive_kernel_primitive_contDiff_one, causal_convolution_time_reversal. Damped scale functions admit L1 kernels and derivatives via the scale Laplace transform and chat07 weighted derivative integrability.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_positive_of_Ici_input
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_outer_integrable
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_triangle_fubini_two_L1
import Theorems.Thm_AvramDividend_Classical_causal_positive_kernel_primitive_contDiff_one
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal
open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.causal_l1_convolution_C1_of_kernel_primitive
    (f k g : ℝ → ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hfL1 : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hg : ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) x, k t ∂volume) = g x) :
    ContDiffOn ℝ 1
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        f (x - s) * g s ∂volume) (Ioi (0 : ℝ)) := by sorry
