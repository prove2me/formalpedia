-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_series_C1_of_signed_power_bounds
-- name    : AvramDividend.Classical.causal_neumann_series_C1_of_signed_power_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:22:42.171068+00:00
-- url     : https://prove2.me/theorems/930f7192-8329-459f-9cf4-f4a87bb6561a
-- title:
--   C1 signed damped Neumann series from quadratic power and primitive estimates
-- statement:
--   If signed causal convolution powers P_n and damped primitives H_n satisfy the quadratic pointwise power and geometric mass estimates, each H_n has the stated derivative and continuous derivative, and the series converges at one positive time, then their sum is C1 on the open interval (ε,R). This provides the precise regularity step in the Gaussian Volterra resolvent construction.
-- source:
--   Compose the Proved causal_neumann_derivative_quadratic_bound, causal_polynomial_geometric_majorant_conversion, and causal_polynomial_geometric_derivative_series_C1.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_neumann_derivative_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_causal_polynomial_geometric_majorant_conversion
import Theorems.Thm_AvramDividend_Classical_causal_polynomial_geometric_derivative_series_C1

open AvramDividend.Classical Set

theorem AvramDividend.Classical.causal_neumann_series_C1_of_signed_power_bounds
    (P H : ℕ → ℝ → ℝ) (a ε R ρ w : ℝ)
    (ha : 0 < a) (hε : 0 < ε)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hP : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hH : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a)
    (hHasDeriv : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      HasDerivAt (H n) (P n x / a - w * H n x) x)
    (hCont : ∀ n : ℕ,
      ContinuousOn (fun x : ℝ => P n x / a - w * H n x) (Ioo ε R))
    (y₀ : ℝ) (hy₀ : y₀ ∈ Ioo ε R)
    (hval : Summable fun n : ℕ => H n y₀) :
    ContDiffOn ℝ 1 (fun y : ℝ => ∑' n : ℕ, H n y) (Ioo ε R) := by sorry
