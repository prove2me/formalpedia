-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_laplace_reciprocal_lower_bound_tendsto
-- name    : AvramDividend.Classical.excursion_laplace_reciprocal_lower_bound_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:43:39.868394+00:00
-- url     : https://prove2.me/theorems/8b7f5d5e-7ac8-4935-9e87-19cc0d8e8a56
-- title:
--   Continuity at zero of the positive-mass reciprocal Laplace lower bound
-- statement:
--   If F is continuous at zero with positive value k, then the extended nonnegative reciprocal 1/F(s) converges to 1/k as s decreases to zero through positive values. Used in the uniform Laplace-to-tightness argument.
-- source:
--   Continuity of inversion away from zero, ENNReal.ofReal, and restriction of a neighbourhood limit to 0+.

import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.ENNReal
open Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.excursion_laplace_reciprocal_lower_bound_tendsto
    (k : ℝ) (hk : 0 < k) (F : ℝ → ℝ)
    (hF0 : F 0 = k) (hFcont : ContinuousAt F 0) :
    Filter.Tendsto (fun s : ℝ => ENNReal.ofReal ((F s)⁻¹))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (k⁻¹))) := by sorry
