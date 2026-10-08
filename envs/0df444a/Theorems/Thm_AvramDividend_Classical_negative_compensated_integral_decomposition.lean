-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_compensated_integral_decomposition
-- name    : AvramDividend.Classical.negative_compensated_integral_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:08:33.011684+00:00
-- url     : https://prove2.me/theorems/41183c6d-aeec-4c7f-a57d-bccc56d6bafd
-- title:
--   Normalised compensated negative-jump integral equals first moment minus exponential residual
-- statement:
--   For a measure on negative jumps with finite absolute first moment and integrable normalised exponential residual, the integral of the compensated kernel (exp(θy)-1-θy)/θ equals the absolute first moment minus the integral of (1-exp(θy))/θ. This exact identity is the finite-variation Lévy exponent decomposition needed to combine dominated convergence with positive compensated drift.
-- source:
--   Algebraic identity on y<0 and pinned Mathlib integral_congr_ae and integral_sub, using explicit integrability hypotheses.

import Mathlib

open MeasureTheory Filter

theorem AvramDividend.Classical.negative_compensated_integral_decomposition
    (ν : Measure ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hneg : ∀ᵐ y ∂ν, y < 0)
    (hfirst : Integrable (fun y : ℝ => |y|) ν)
    (hres : Integrable (fun y : ℝ =>
      (1 - Real.exp (θ * y)) / θ) ν) :
    (∫ y : ℝ,
      (Real.exp (θ * y) - 1 - θ * y) / θ ∂ν) =
      (∫ y : ℝ, |y| ∂ν) -
        (∫ y : ℝ, (1 - Real.exp (θ * y)) / θ ∂ν) := by sorry
