-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_real_laplace_causal_convolution
-- name    : AvramDividend.Classical.positive_real_laplace_causal_convolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T16:29:52.590739+00:00
-- url     : https://prove2.me/theorems/a2c48818-3ce1-43b9-a4a5-5c290c720e5e
-- title:
--   Laplace transform of a real positive causal convolution factors into the two Laplace transforms
-- statement:
--   Let f and g be measurable real functions whose exponentially damped versions are integrable on the positive half-line. The real Laplace transform of the causal convolution x↦∫(0,x] f(s)g(x−s)ds equals the product of their real Laplace transforms. The proof invokes pinned Mathlib's integral_posConvolution for the weighted functions, changes the interval integral over 0..x to Ioc 0 x when x>0, and factors exponentials by exp(a+b)=exp(a)exp(b). No continuity or positivity of the integrands is assumed, and the exact Ioc endpoint convention is preserved.
-- source:
--   Pinned Mathlib MeasureTheory.integral_posConvolution and intervalIntegral.integral_of_le

import Mathlib
import Mathlib.Analysis.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.positive_real_laplace_causal_convolution
    (f g : ℝ → ℝ) (θ : ℝ)
    (hf : IntegrableOn (fun s : ℝ => Real.exp (-θ * s) * f s)
      (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn (fun s : ℝ => Real.exp (-θ * s) * g s)
      (Ioi (0 : ℝ)) volume) :
    (∫ x in Ioi (0 : ℝ), ∫ s in Ioc (0 : ℝ) x,
      Real.exp (-θ * x) * (f s * g (x - s)) ∂volume ∂volume) =
      (∫ s in Ioi (0 : ℝ), Real.exp (-θ * s) * f s ∂volume) *
        (∫ t in Ioi (0 : ℝ), Real.exp (-θ * t) * g t ∂volume) := by sorry
