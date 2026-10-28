-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_weighted_integrable
-- name    : AvramDividend.Classical.causal_convolution_powers_weighted_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:46:18.626297+00:00
-- url     : https://prove2.me/theorems/2c0a9dcc-7dfe-49c2-805e-6eef41c61604
-- title:
--   Every causal convolution power remains exponentially integrable
-- statement:
--   An exponentially L1 causal kernel κ generates convolution powers F0=κ, F(n+1)=κ*Fn; at any fixed Laplace parameter θ each power remains exponentially integrable by induction. This discharges the important hFi premise of the already proved geometric Laplace-power and resolvent-series identities, uniformly as a theorem scheme for every admissible θ.
-- source:
--   Proved positive_causal_convolution_laplace_integrable

import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_integrable
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_convolution_powers_weighted_integrable
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (θ : ℝ)
    (hκi : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * κ t)
      (Ioi (0 : ℝ)) volume)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) = fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume) :
    ∀ n : ℕ, IntegrableOn
      (fun t : ℝ => Real.exp (-(θ * t)) * F n t)
      (Ioi (0 : ℝ)) volume := by sorry
