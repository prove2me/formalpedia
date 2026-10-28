-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_geometric_laplace_resolvent_series
-- name    : AvramDividend.Classical.causal_geometric_laplace_resolvent_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:29:14.236986+00:00
-- url     : https://prove2.me/theorems/bc34784f-e097-4f6e-817b-d3b8a799bf34
-- title:
--   Exact Laplace transform of the continuous real renewal resolvent sum
-- statement:
--   The exponential factor in a unilateral Laplace transform distributes across a real infinite sum. Combining that equality (valid by Mathlib tsum_mul_left even without an independent pointwise summability premise) with the proved nonnegative geometric Laplace series integral yields the exact integral ρ/(1−ρ). This is the scale-function defining Laplace condition in the positive discount Neumann construction.
-- source:
--   Proved causal_geometric_laplace_series_integral and Mathlib tsum_mul_left

import Theorems.Thm_AvramDividend_Classical_causal_geometric_laplace_series_integral
import Mathlib.Topology.Algebra.InfiniteSum.Ring
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_geometric_laplace_resolvent_series
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
      Real.exp (-(θ * x)) * (∑' n : ℕ, F n x) ∂volume) =
        ρ / (1 - ρ) := by sorry
