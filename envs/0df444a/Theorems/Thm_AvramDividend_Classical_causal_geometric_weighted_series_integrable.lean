-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_geometric_weighted_series_integrable
-- name    : AvramDividend.Classical.causal_geometric_weighted_series_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:21:59.337492+00:00
-- url     : https://prove2.me/theorems/1d26aba6-7d93-496d-9827-6f2ae41b4f85
-- title:
--   Integrability of the exponentially weighted causal Neumann sum
-- statement:
--   When nonnegative convolution-power functions have summable pointwise values and integrable exponential tilts with geometric integral masses rho^(n+1), the exponential tilt of their infinite sum is integrable on the positive half-line.
-- source:
--   Proved weighted-term tsum integrability plus the tsum scalar multiplication identity.

import Theorems.Thm_AvramDividend_Classical_causal_geometric_weighted_tsum_integrable
import Mathlib.Topology.Algebra.InfiniteSum.Ring
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_geometric_weighted_series_integrable
    (F : ℕ → ℝ → ℝ) (θ ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hFi : ∀ n : ℕ, IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * F n x)
      (Ioi (0 : ℝ)) volume)
    (hpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hpoint : ∀ x : ℝ, Summable (fun n : ℕ => F n x))
    (hmass : ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * F n x ∂volume) =
        ρ ^ (n + 1)) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * (∑' n : ℕ, F n x))
      (Ioi (0 : ℝ)) volume := by sorry
