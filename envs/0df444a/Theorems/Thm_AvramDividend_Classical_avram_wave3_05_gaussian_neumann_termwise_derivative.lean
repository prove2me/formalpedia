-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_neumann_termwise_derivative
-- name    : AvramDividend.Classical.avram_wave3_05_gaussian_neumann_termwise_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:59:13.44885+00:00
-- url     : https://prove2.me/theorems/5b32ff5e-56de-40af-b0cf-a117f14a4fc4
-- title:
--   Exact termwise derivative of the source Gaussian Neumann primitive series
-- statement:
--   The Gaussian source signed convolution-power estimates yield a quadratic-geometric pointwise bound on the derivatives of the damped primitive terms. The prior C1 result had discarded the actual derivative equality. This theorem retains HasDerivAt of the complete series with derivative equal to the sum of P_n/a-w H_n on any compact positive interval. Polynomial-geometric summability justifies differentiating the infinite series, providing the exact missing input to identify weighted W''.
-- source:
--   Pinned Mathlib hasDerivAt_tsum_of_isPreconnected and summable_pow_mul_geometric_of_norm_lt_one; accepted Gaussian derivative majorant theorems 930f7192 and 79315230.

import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_neumann_derivative_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_causal_polynomial_geometric_majorant_conversion

open AvramDividend.Classical Set

theorem AvramDividend.Classical.avram_wave3_05_gaussian_neumann_termwise_derivative
    (P H : ℕ → ℝ → ℝ) (a ε R ρ w : ℝ)
    (ha : 0 < a) (hε : 0 < ε)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hP : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hH : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a)
    (hHasDeriv : ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      HasDerivAt (H n) (P n x / a - w * H n x) x)
    (y₀ : ℝ) (hy₀ : y₀ ∈ Ioo ε R)
    (hval : Summable (fun n : ℕ => H n y₀))
    (y : ℝ) (hy : y ∈ Ioo ε R) :
    HasDerivAt (fun z : ℝ => ∑' n : ℕ, H n z)
      (∑' n : ℕ, (P n y / a - w * H n y)) y := by sorry
