-- Prove2me | Theorems.Thm_AvramDividend_Classical_hasDerivAt_pos_eventually_forward_scale_gap
-- name    : AvramDividend.Classical.hasDerivAt_pos_eventually_forward_scale_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:11:49.343488+00:00
-- url     : https://prove2.me/theorems/551736fc-fa83-4991-a581-6bd7d13fc814
-- title:
--   Positive derivative makes forward scale finite differences eventually positive
-- statement:
--   For a differentiable real-valued function W with strictly positive derivative at a, every sufficiently small positive forward displacement ε gives a strictly positive increment W(a+ε)-W(a). This elementary but important side condition makes the right stopped-renewal finite-difference denominator positive near zero; the model-specific scale-function derivative positivity must be supplied separately.
-- source:
--   Mathlib HasDerivAt.tendsto_slope_zero_right, Filter.Tendsto.eventually_const_lt and positivity of real inverses.

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.GroupWithZero.Basic

open Filter Topology

theorem AvramDividend.Classical.hasDerivAt_pos_eventually_forward_scale_gap
    (W : ℝ → ℝ) (a d : ℝ)
    (hD : HasDerivAt W d a) (hd : 0 < d) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < W (a + ε) - W a := by sorry
