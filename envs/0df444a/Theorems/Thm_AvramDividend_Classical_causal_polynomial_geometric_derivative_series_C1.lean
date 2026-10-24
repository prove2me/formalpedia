-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_polynomial_geometric_derivative_series_C1
-- name    : AvramDividend.Classical.causal_polynomial_geometric_derivative_series_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:42:17.645997+00:00
-- url     : https://prove2.me/theorems/79315230-1fc8-4c81-9fcc-8a8bafc2bb7f
-- title:
--   C1 regularity of a causal Neumann series under quadratic-geometric derivative bounds
-- statement:
--   A series of differentiable terms on an open real interval is C1 if its derivatives are continuous, dominated uniformly by C(n²+1)rⁿ with 0≤r<1, and the original series converges at one point. The polynomial-geometric summability is strong enough for uniform convergence of the derivative series and termwise differentiation.
-- source:
--   Direct derivative-series bridge for Gaussian Volterra C2: the simplex estimate naturally produces n² times a geometric convolution mass.

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.InfiniteSum.Ring

open Set

theorem AvramDividend.Classical.causal_polynomial_geometric_derivative_series_C1
    (g g' : ℕ → ℝ → ℝ) (a b C r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hg : ∀ n y, y ∈ Ioo a b → HasDerivAt (g n) (g' n y) y)
    (hg' : ∀ n, ContinuousOn (g' n) (Ioo a b))
    (hbound : ∀ n y, y ∈ Ioo a b →
      ‖g' n y‖ ≤ C * (((n : ℝ) ^ 2 + 1) * r ^ n))
    (y₀ : ℝ) (hy₀ : y₀ ∈ Ioo a b)
    (hval : Summable fun n => g n y₀) :
    ContDiffOn ℝ 1 (fun y => ∑' n, g n y) (Ioo a b) := by sorry
