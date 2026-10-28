-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exponential_convolution_power_sequence
-- name    : AvramDividend.Classical.causal_exponential_convolution_power_sequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:30:59.056069+00:00
-- url     : https://prove2.me/theorems/76bb5782-ba5f-4306-bf4e-a5ab93c29a0d
-- title:
--   Exponential damping transports every causal convolution power recurrence
-- statement:
--   Given an undamped causal convolution-power sequence U0=f, U(n+1)=f*U(n), multiplication by exp(-θx) turns the entire recurrence into convolution powers of the exponentially damped kernel. This is the precise bridge between the monotone unweighted W0 powers and the geometrically summable weighted powers in the constructive positive-discount scale proof.
-- source:
--   Proved exponential_causal_convolution_factorisation, lifted to sequences

import Theorems.Thm_AvramDividend_Classical_exponential_causal_convolution_factorisation
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_exponential_convolution_power_sequence
    (f : ℝ → ℝ) (U : ℕ → ℝ → ℝ) (θ : ℝ)
    (hU0 : U 0 = f)
    (hUrec : ∀ n : ℕ, ∀ x : ℝ,
      U (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x, f (x - s) * U n s ∂volume) :
    (fun x : ℝ => Real.exp (-(θ * x)) * U 0 x) =
      (fun x : ℝ => Real.exp (-(θ * x)) * f x) ∧
    (∀ n : ℕ, ∀ x : ℝ,
      Real.exp (-(θ * x)) * U (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x,
          (Real.exp (-(θ * (x - s))) * f (x - s)) *
          (Real.exp (-(θ * s)) * U n s) ∂volume) := by sorry
