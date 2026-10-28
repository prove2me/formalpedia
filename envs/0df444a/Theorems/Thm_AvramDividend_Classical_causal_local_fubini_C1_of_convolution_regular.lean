-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_local_fubini_C1_of_convolution_regular
-- name    : AvramDividend.Classical.causal_local_fubini_C1_of_convolution_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:51:43.445333+00:00
-- url     : https://prove2.me/theorems/d88dacb5-8ede-402e-9552-62110ce7ea68
-- title:
--   Local finite-horizon Fubini smoothing of a causal convolution with regular derivative convolution
-- statement:
--   Finite-horizon causal Fubini proves that the convolution with the primitive g of a locally integrable kernel k is itself the time primitive of J=f*k. If J is continuous on positive times and integrable on every interval from zero, the existing causal-primitive theorem makes f*g C1 for all positive times. No global L1 hypotheses or boundedness-at-zero derivative assumptions are needed. This isolates the genuine remaining continuity/integrability work for the original monotone C1 kernel theorem.
-- source:
--   Proved causal_l1_kernel_triangle_fubini_two_local_L1 [77c56cc3-bcfe-437c-8b4c-d0da9e79711f], causal_positive_kernel_primitive_contDiff_one [ca82cbc5-5a02-4693-8a41-c18087e20c09], causal_convolution_time_reversal [f1622c94-540f-40cd-980d-3b1132ca67c4]. Open target causal_convolution_contDiffOn_one_of_monotone_C1_kernel [df538b19-3214-472b-a34c-c964a375643e].

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_triangle_fubini_two_local_L1
import Theorems.Thm_AvramDividend_Classical_causal_positive_kernel_primitive_contDiff_one
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal
open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.causal_local_fubini_C1_of_convolution_regular
    (f k g : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 < x → IntegrableOn f (Ioc (0 : ℝ) x) volume)
    (hk : ∀ x : ℝ, 0 < x → IntegrableOn k (Ioc (0 : ℝ) x) volume)
    (hg : ∀ x : ℝ, 0 < x →
      (∫ s in Ioc (0 : ℝ) x, k s ∂volume) = g x)
    (J : ℝ → ℝ)
    (hJ : ∀ x : ℝ, 0 < x →
      J x = ∫ s in Ioc (0 : ℝ) x, f (x - s) * k s ∂volume)
    (hJcont : ContinuousOn J (Ioi (0 : ℝ)))
    (hJint : ∀ x : ℝ, 0 < x → IntervalIntegrable J volume 0 x) :
    ContDiffOn ℝ 1
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume)
      (Ioi (0 : ℝ)) := by sorry
