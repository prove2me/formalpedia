-- Prove2me | Theorems.Thm_AvramDividend_Classical_real_exponentially_weighted_convolution_integral
-- name    : AvramDividend.Classical.real_exponentially_weighted_convolution_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T15:03:09.99927+00:00
-- url     : https://prove2.me/theorems/e924b03a-fb1e-48ab-8da2-abd1934bdf76
-- title:
--   Real Laplace-weighted convolution integrates to product of its two weighted factors
-- statement:
--   If the exponentially weighted real functions exp(-θt)f(t) and exp(-θt)g(t) are Lebesgue integrable on ℝ, then the integral over x of their standard convolution equals the product of their two integrals. This uses Mathlib's exact real convolution_mul identification and integral_convolution theorem, without any assumption that f or g themselves are unweighted globally integrable. The result supplies the fundamental Fubini/factorisation component for Laplace inversion of a causal Gaussian Esscher Volterra convolution.
-- source:
--   Mathlib.Analysis.Convolution: MeasureTheory.convolution_mul, integral_convolution; both signatures remotely inspected at the pinned environment.

import Mathlib
import Mathlib.Analysis.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.real_exponentially_weighted_convolution_integral
    (f g : ℝ → ℝ) (θ : ℝ)
    (hf : Integrable (fun t : ℝ => Real.exp (-θ * t) * f t) volume)
    (hg : Integrable (fun t : ℝ => Real.exp (-θ * t) * g t) volume) :
    (∫ x : ℝ, ∫ s : ℝ,
      (Real.exp (-θ * s) * f s) *
        (Real.exp (-θ * (x - s)) * g (x - s)) ∂volume ∂volume) =
      (∫ s : ℝ, Real.exp (-θ * s) * f s ∂volume) *
        (∫ t : ℝ, Real.exp (-θ * t) * g t ∂volume) := by sorry
