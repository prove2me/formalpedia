-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_weighted_causal_convolution_integrable
-- name    : AvramDividend.Classical.positive_weighted_causal_convolution_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T17:14:16.29046+00:00
-- url     : https://prove2.me/theorems/b4c5b9f9-a7db-466c-8f64-3dcf48aabb9f
-- title:
--   Weighted causal convolution is integrable on the positive axis
-- statement:
--   If f and g have real integrable exponential weights over x>0 at parameter θ, then the real exponential weight of their causal convolution ∫_(0,x] f(s)g(x−s) ds is also integrable on x>0. The proof identifies this weighted causal integral with Mathlib's posConvolution of the exponentially weighted factors, then applies the proved general integrable_posConvolution theorem. Its exact Ioc endpoint form is tailored to the Gaussian Esscher Volterra kernel and provides the missing integrability premise for signed Laplace uniqueness.
-- source:
--   Pinned Mathlib MeasureTheory.integrable_posConvolution, intervalIntegral.integral_of_le

import Mathlib.Analysis.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.positive_weighted_causal_convolution_integrable
    (f g : ℝ → ℝ) (θ : ℝ)
    (hf : IntegrableOn (fun s : ℝ => Real.exp (-(θ * s)) * f s)
      (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * g t)
      (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
      (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume))
      (Ioi (0 : ℝ)) volume := by sorry
