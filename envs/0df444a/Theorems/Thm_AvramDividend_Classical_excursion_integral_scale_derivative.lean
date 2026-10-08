-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_integral_scale_derivative
-- name    : AvramDividend.Classical.excursion_integral_scale_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:43:16.804536+00:00
-- url     : https://prove2.me/theorems/5b518605-2d32-4801-bab0-23a8678c4a9b
-- title:
--   Differentiating a continuous excursion-tail exponential interval representation
-- statement:
--   Pure real-analysis bridge: continuity of the excursion-tail function on the positive half-line and the interval exponential representation imply the pointwise HasDerivAt product formula. Choose an anchor a strictly between zero and x and use the representation for all nearby y; the fundamental theorem of calculus and chain/product rules supply the derivative. No Levy-process probability theory is needed.
-- source:
--   Fundamental theorem of calculus for continuous interval integrands, exponential chain rule; analytic consequence of the excursion representation in Chan, Kyprianou, Savov (2011), equation (5).

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.excursion_integral_scale_derivative
    (W : ℝ → ℝ) (φ : ℝ) (μ : Measure ℝ)
    (hcont : ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0))
    (hexp : ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Ici t))) :
    ∀ x : ℝ, 0 < x →
      HasDerivAt W (W x * (φ + μ.real (Ici x))) x := by sorry
