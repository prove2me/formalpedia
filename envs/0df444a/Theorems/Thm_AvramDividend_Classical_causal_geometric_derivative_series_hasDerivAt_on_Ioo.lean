-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_geometric_derivative_series_hasDerivAt_on_Ioo
-- name    : AvramDividend.Classical.causal_geometric_derivative_series_hasDerivAt_on_Ioo
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:01:41.884311+00:00
-- url     : https://prove2.me/theorems/ad50389d-adae-447a-a525-6f70bacb234b
-- title:
--   Termwise derivative of a locally geometric Neumann series on an open interval
-- statement:
--   An infinite series of differentiable real functions on an open interval is termwise differentiable if one series value is summable and all derivative terms have a uniform geometric majorant C r^n with 0≤r<1. This is the convergence bridge needed for the weighted causal Volterra Neumann resolvent away from zero.
-- source:
--   Local geometric-series specialisation of the pinned Mathlib hasDerivAt_tsum_of_isPreconnected theorem, preparatory to C1 Gaussian Volterra resolvent regularity.

import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.InfiniteSum.Ring

open Set

theorem AvramDividend.Classical.causal_geometric_derivative_series_hasDerivAt_on_Ioo
    (g g' : ℕ → ℝ → ℝ) (a b C r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hg : ∀ n y, y ∈ Ioo a b → HasDerivAt (g n) (g' n y) y)
    (hbound : ∀ n y, y ∈ Ioo a b → ‖g' n y‖ ≤ C * r ^ n)
    (y₀ : ℝ) (hy₀ : y₀ ∈ Ioo a b)
    (hval : Summable fun n => g n y₀)
    (y : ℝ) (hy : y ∈ Ioo a b) :
    HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n y) y := by sorry
