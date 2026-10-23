-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_causal_laplace_local_le_product
-- name    : AvramDividend.Classical.positive_causal_laplace_local_le_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:02:33.098288+00:00
-- url     : https://prove2.me/theorems/e3450378-50e3-4556-a3ae-53f0db8f1853
-- title:
--   Local positive causal Laplace convolution is bounded by product of weighted global integrals
-- statement:
--   For nonnegative real f,g on (0,∞), each possessing exponentially weighted L1 transforms, and any finite horizon R≥0, the Laplace-weighted convolution integrated over x∈(0,R] is at most the product of the two globally integrated Laplace weights. The full positive convolution integral factors by the already-Proved signed Laplace convolution product theorem. Nonnegativity allows monotonicity under restriction to the smaller outer interval (0,R]. This is the central finite-horizon Young-type inequality required for contractive Volterra uniqueness.
-- source:
--   Proved positive_real_laplace_causal_convolution, positive_weighted_causal_convolution_integrable; pinned Mathlib setIntegral_mono_set

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_real_laplace_causal_convolution
import Theorems.Thm_AvramDividend_Classical_positive_weighted_causal_convolution_integrable
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.positive_causal_laplace_local_le_product
    (f g : ℝ → ℝ) (θ R : ℝ) (hR : 0 ≤ R)
    (hf : IntegrableOn (fun t : ℝ => Real.exp (-θ * t) * f t)
      (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn (fun t : ℝ => Real.exp (-θ * t) * g t)
      (Ioi (0 : ℝ)) volume)
    (hfn : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    (hgn : ∀ t : ℝ, 0 ≤ t → 0 ≤ g t) :
    (∫ x in Ioc (0 : ℝ) R, Real.exp (-θ * x) *
      (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume) ∂volume) ≤
      (∫ s in Ioi (0 : ℝ), Real.exp (-θ * s) * f s ∂volume) *
      (∫ t in Ioi (0 : ℝ), Real.exp (-θ * t) * g t ∂volume) := by sorry
