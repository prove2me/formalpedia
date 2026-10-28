-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_geometric_laplace_series_integral
-- name    : AvramDividend.Classical.causal_geometric_laplace_series_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:24:33.307992+00:00
-- url     : https://prove2.me/theorems/fe714e6c-82ac-4b4d-a625-863cbf17a54e
-- title:
--   Exact Laplace integral of the nonnegative geometric renewal sum
-- statement:
--   For nonnegative causal renewal powers Fn with exponentially weighted L1 integrability and exact weighted Laplace masses ρ^(n+1), 0≤ρ<1, the integrated nonnegative infinite sum of those weighted powers equals ρ/(1−ρ). This combines the established Tonelli sum-integral exchange and geometric renewal mass evaluation, providing the main all-parameter Laplace step of positive-q scale construction.
-- source:
--   Proved nonnegative_renewal_integral_tsum_exchange and causal_geometric_renewal_total_mass_sum

import Theorems.Thm_AvramDividend_Classical_nonnegative_renewal_integral_tsum_exchange
import Theorems.Thm_AvramDividend_Classical_causal_geometric_renewal_total_mass_sum
import Mathlib.Analysis.SpecificLimits.Basic
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_geometric_laplace_series_integral
    (F : ℕ → ℝ → ℝ) (θ ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hFi : ∀ n : ℕ, IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * F n x)
      (Ioi (0 : ℝ)) volume)
    (hpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hmass : ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * F n x ∂volume) =
        ρ ^ (n + 1)) :
    (∫ x in Ioi (0 : ℝ),
      ∑' n : ℕ, Real.exp (-(θ * x)) * F n x ∂volume) =
        ρ / (1 - ρ) := by sorry
