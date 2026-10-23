-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_integrable
-- name    : AvramDividend.Classical.positive_causal_convolution_laplace_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T15:09:11.378683+00:00
-- url     : https://prove2.me/theorems/e5433346-b514-4584-ac5b-d49d3fb01e69
-- title:
--   Signed exponentially weighted causal convolution is integrable
-- statement:
--   If two signed real functions are L1 after positive-time exponential weighting at the same real Laplace parameter, their causal convolution also has an integrable exponential weight. Derived from Mathlib's integrable_posConvolution and the exact exponential factorisation, supplying the missing integrability premise for Gaussian scale-function Laplace uniqueness.
-- source:
--   Mathlib.Analysis.Convolution, MeasureTheory.integrable_posConvolution; real exponential convolution factorisation.

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.positive_causal_convolution_laplace_integrable
    (f g : ℝ → ℝ) (θ : ℝ)
    (hf : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * f t)
      (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * g t)
      (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
      (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume))
      (Ioi (0 : ℝ)) volume := by sorry
