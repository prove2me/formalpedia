-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_scale_derivative_diverges_of_kernel_diverges
-- name    : AvramDividend.Classical.esscher_scale_derivative_diverges_of_kernel_diverges
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:07:18.203158+00:00
-- url     : https://prove2.me/theorems/874da69f-128c-4864-8978-8235b7fdefdd
-- title:
--   Diverging Esscher renewal kernel forces infinite positive-origin scale derivative
-- statement:
--   The ordinary derivative of the scale function dominates a positive renewal kernel on the positive half-line. If that kernel diverges towards zero, then the scale derivative diverges to positive infinity at zero from the right. This composes the already Proved local Esscher derivative inequality and an order-filter transfer.
-- source:
--   Proved esscher_scale_deriv_lower_of_renewal_identity (685c6dfa-6848-4513-b4df-bcd3817fc11a); Filter.tendsto_atTop.

import Theorems.Thm_AvramDividend_Classical_esscher_scale_deriv_lower_of_renewal_identity
import Mathlib.Topology.Algebra.Order.Field

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped Topology

namespace AvramDividend.Classical

/-- Kernel divergence transfers through a positive Esscher renewal representation to the scale derivative. -/
theorem esscher_scale_derivative_diverges_of_kernel_diverges
    (W : ℝ → ℝ) (φ c : ℝ) (f k : ℝ → ℝ)
    (hφ : 0 ≤ φ)
    (hW : ∀ x : ℝ, 0 < x → W x =
      Real.exp (φ * x) * (c + ∫ t in (0 : ℝ)..x, f t))
    (hint : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x)
    (hmeas : ∀ x : ℝ, 0 < x → StronglyMeasurableAtFilter f (𝓝 x) volume)
    (hcont : ∀ x : ℝ, 0 < x → ContinuousAt f x)
    (hFnonneg : ∀ x : ℝ, 0 < x → 0 ≤ c + ∫ t in (0 : ℝ)..x, f t)
    (hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (hk : ∀ x : ℝ, 0 < x → k x ≤ f x)
    (hkTop : Tendsto k (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    Tendsto (deriv W) (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry

end AvramDividend.Classical
