-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_integrated_density_derivative_lower
-- name    : AvramDividend.Classical.esscher_integrated_density_derivative_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:14:33.353972+00:00
-- url     : https://prove2.me/theorems/ded14437-3cf3-4404-b8fa-2a1b800dade9
-- title:
--   An Esscher-exponential tilted cumulative dominates its nonnegative density derivative
-- statement:
--   A positive exponential Esscher tilt of a nonnegative cumulative real density has ordinary derivative at any nonnegative point at least as large as the local density, and hence dominates any pointwise density lower bound. This isolates the calculus step needed to carry a causal renewal-kernel lower bound to the bounded-variation q-scale derivative.
-- source:
--   The fundamental theorem of calculus and derivative of the exponential in pinned Mathlib; Avram–Palmowski–Pistorius (2007), canonical BV Esscher renewal density route.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
open AvramDividend.Classical MeasureTheory intervalIntegral Filter
open scoped Topology

namespace AvramDividend.Classical

/-- A nonnegative Esscher tilt preserves a lower bound for a positive-axis cumulative density. -/
theorem esscher_integrated_density_derivative_lower
    (φ c x : ℝ) (f : ℝ → ℝ) (k : ℝ)
    (hφ : 0 ≤ φ) (hx : 0 ≤ x)
    (hint : IntervalIntegrable f volume 0 x)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 x) volume)
    (hcont : ContinuousAt f x)
    (hFnonneg : 0 ≤ c + ∫ t in (0 : ℝ)..x, f t)
    (hfnonneg : 0 ≤ f x) (hk : k ≤ f x) :
    k ≤ deriv
      (fun y : ℝ => Real.exp (φ * y) *
        (c + ∫ t in (0 : ℝ)..y, f t)) x := by sorry

end AvramDividend.Classical
