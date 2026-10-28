-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_laplace_geometric
-- name    : AvramDividend.Classical.causal_convolution_powers_laplace_geometric
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:20:13.751994+00:00
-- url     : https://prove2.me/theorems/559a960e-56b5-4007-988e-c4ee847f8df9
-- title:
--   Exact geometric Laplace transform of every causal convolution power
-- statement:
--   If F0 is a kernel κ and F(n+1) its causal real convolution with κ, with integrability of all exponentially weighted powers and base Laplace mass A, then the Laplace transform of Fn at the same θ equals A^(n+1). An induction with the established signed causal convolution Laplace product rule supplies the analytic transform sequence used to construct every positive-discount scale from W0.
-- source:
--   AvramDividend.Classical.positive_causal_convolution_laplace_product (Proved)

import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_product
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_convolution_powers_laplace_geometric
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (θ A : ℝ)
    (hκi : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * κ t)
      (Ioi (0 : ℝ)) volume)
    (hFi : ∀ n : ℕ, IntegrableOn
      (fun t : ℝ => Real.exp (-(θ * t)) * F n t)
      (Ioi (0 : ℝ)) volume)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) = fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume)
    (hκmass : (∫ t in Ioi (0 : ℝ), Real.exp (-(θ * t)) * κ t ∂volume) = A) :
    ∀ n : ℕ,
      (∫ t in Ioi (0 : ℝ), Real.exp (-(θ * t)) * F n t ∂volume) =
        A ^ (n + 1) := by sorry
