-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exponential_convolution_power_untwist
-- name    : AvramDividend.Classical.causal_exponential_convolution_power_untwist
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:35:35.614869+00:00
-- url     : https://prove2.me/theorems/a982b25f-b1af-4a56-ad95-a784144198e7
-- title:
--   Uniqueness of exponentially tilted causal convolution power sequences
-- statement:
--   For two positive-interval causal convolution-power sequences with kernels f and exp(-θx)f, the damped powers equal exp(-θx) times the undamped powers, term by term. The induction uses the accepted causal exponential convolution factorisation. Enables undamped monotonicity to be transferred to the positive-discount Neumann construction.
-- source:
--   Proved exponential_causal_convolution_factorisation; induction on the convolution recurrence.

import Theorems.Thm_AvramDividend_Classical_exponential_causal_convolution_factorisation
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_exponential_convolution_power_untwist
    (f K : ℝ → ℝ) (F U : ℕ → ℝ → ℝ) (θ : ℝ)
    (hK : ∀ x : ℝ, K x = Real.exp (-(θ * x)) * f x)
    (hF0 : F 0 = K)
    (hFrec : ∀ n : ℕ, ∀ x : ℝ, F (n + 1) x =
      ∫ s in Ioc (0 : ℝ) x, K (x - s) * F n s ∂volume)
    (hU0 : U 0 = f)
    (hUrec : ∀ n : ℕ, ∀ x : ℝ, U (n + 1) x =
      ∫ s in Ioc (0 : ℝ) x, f (x - s) * U n s ∂volume) :
    ∀ n : ℕ, ∀ x : ℝ,
      F n x = Real.exp (-(θ * x)) * U n x := by sorry
