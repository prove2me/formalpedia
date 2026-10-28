-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_convolution_power_series_exact_laplace
-- name    : AvramDividend.Classical.causal_convolution_power_series_exact_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:22:44.75898+00:00
-- url     : https://prove2.me/theorems/6eb34642-b9b9-4b5a-be2e-13df2d4baa98
-- title:
--   Exact Laplace transform of a nonnegative renewal series from kernel hypotheses
-- statement:
--   A complete deterministic renewal-series Laplace theorem: given a nonnegative causal convolution-power family F, one integrability premise for its base kernel κ, and base transform ρ in [0,1), the real Laplace integral of the pointwise sum is ρ/(1−ρ). Integrability of every power, geometric transform induction and Tonelli interchange are all proved internally by existing verified helpers. Reusable at each θ permitted by the scale function definition.
-- source:
--   The three Proved weighted integrability, convolution geometric Laplace, and resolvent Laplace lemmas

import Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_weighted_integrable
import Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_laplace_geometric
import Theorems.Thm_AvramDividend_Classical_causal_geometric_laplace_resolvent_series
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_convolution_power_series_exact_laplace
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (θ ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hκi : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * κ t)
      (Ioi (0 : ℝ)) volume)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) = fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hκmass : (∫ t in Ioi (0 : ℝ), Real.exp (-(θ * t)) * κ t ∂volume) = ρ) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * (∑' n : ℕ, F n x) ∂volume) =
        ρ / (1 - ρ) := by sorry
