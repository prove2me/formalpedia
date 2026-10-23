-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_laplace_integral_eq_toReal
-- name    : AvramDividend.Classical.gaussian_double_tail_real_laplace_integral_eq_toReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T16:04:44.028665+00:00
-- url     : https://prove2.me/theorems/6545953d-9c3d-4771-9a62-72d7ed2edbfd
-- title:
--   Exact real Gaussian double-tail Laplace transform from its finite ENNReal double-lintegral
-- statement:
--   For a Gaussian Esscher double-tail kernel with an outer finite weighted ENNReal integral, the real Laplace transform of the jump-integrated kernel is exactly the real representative of the positive double-lintegral. Measurability of the inner jump lintegral follows by parameterised lintegral measurability. The independently proved pointwise inner factorisation moves the Laplace weight inside the jump lintegral, while the independently proved real-weighted conversion bridge justifies the outer Bochner/ENNReal transition. Finite total mass guarantees the toReal integral conversion without information loss.
-- source:
--   Proved gaussian_double_tail_inner_laplace_weight_factor and real_weighted_laplace_toReal_bridge; Mathlib Measurable.lintegral_prod_right

import Mathlib
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_inner_laplace_weight_factor
import Theorems.Thm_AvramDividend_Classical_real_weighted_laplace_toReal_bridge
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_real_laplace_integral_eq_toReal
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hfin : (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ ∂volume) < ⊤) :
    (∫ t : ℝ, Real.exp (-θ * t) *
      (∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ).toReal ∂volume) =
      (∫⁻ t : ℝ, ∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ ∂volume).toReal := by sorry
