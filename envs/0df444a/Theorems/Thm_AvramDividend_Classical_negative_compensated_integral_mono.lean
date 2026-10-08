-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_compensated_integral_mono
-- name    : AvramDividend.Classical.negative_compensated_integral_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:18:14.291959+00:00
-- url     : https://prove2.me/theorems/6aaa2254-50e1-48d7-a5b0-02ba6c348713
-- title:
--   Normalised compensated negative-jump integral increases with real Laplace parameter
-- statement:
--   For a real-jump measure supported almost everywhere on negative values, and positive real Laplace parameters θ₁≤θ₂, the integrals of the normalised compensated exponential kernel are ordered whenever both are Bochner-integrable. This extends the discrete-parameter divergence estimate to every larger real parameter, provided the canonical Lévy-jump integrability has been established.
-- source:
--   Pointwise Prove2Me-Proved compensated secant monotonicity, integrated using the pinned Mathlib integral_mono_ae under the stated exact integrability assumptions. Useful for eventual ψ growth beyond integer Laplace parameters.

import Mathlib

open MeasureTheory Filter

theorem AvramDividend.Classical.negative_compensated_integral_mono
    (ν : Measure ℝ) (θ₁ θ₂ : ℝ)
    (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ₂)
    (hneg : ∀ᵐ y ∂ν, y < 0)
    (hi₁ : Integrable (fun y : ℝ =>
      (Real.exp (θ₁ * y) - 1 - θ₁ * y) / θ₁) ν)
    (hi₂ : Integrable (fun y : ℝ =>
      (Real.exp (θ₂ * y) - 1 - θ₂ * y) / θ₂) ν) :
    (∫ y : ℝ, (Real.exp (θ₁ * y) - 1 - θ₁ * y) / θ₁ ∂ν) ≤
      ∫ y : ℝ, (Real.exp (θ₂ * y) - 1 - θ₂ * y) / θ₂ ∂ν := by sorry
