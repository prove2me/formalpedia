-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_ae_finite
-- name    : AvramDividend.Classical.gaussian_double_tail_kernel_ae_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:41:37.623221+00:00
-- url     : https://prove2.me/theorems/3bb373e2-9c13-4bee-9e1d-36bdf9e1d46b
-- title:
--   Almost-everywhere finiteness of Gaussian Esscher double-tail kernel
-- statement:
--   Under the Lévy truncated-square integrability condition, φ>0 and positive Laplace parameter θ, the exponentially damped Gaussian double-tail inner jump integral is finite at almost every time t. The separately published finite time-first double-tail integral gives an integrable nonnegative parameter function. Prove that function is measurable using pinned Measurable.lintegral_prod_right, then use pinned MeasureTheory.ae_lt_top.
-- source:
--   Depends on Proved gaussian_double_tail_esscher_laplace_inner_finite; exact Mathlib revision ae_lt_top and Measurable.lintegral_prod_right inspected.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_kernel_ae_finite
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 < θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    ∀ᵐ t : ℝ ∂volume,
      (∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ) < ⊤ := by sorry
