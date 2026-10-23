-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_kernel_toReal_integrable
-- name    : AvramDividend.Classical.gaussian_esscher_kernel_toReal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T12:12:28.048417+00:00
-- url     : https://prove2.me/theorems/be0210ee-0d17-44fe-a01d-74245a66dabb
-- title:
--   Real L1 integrability of the Gaussian Esscher double-tail kernel
-- statement:
--   The real-valued positive Gaussian Esscher double-tail kernel obtained by converting each ENNReal jump integral to Real is integrable over the time line. The inner nonnegative integral is measurable by measurable_lintegral_prod_right, and its total lintegral is finite by the global Gaussian double-tail mass theorem. Pinned Mathlib integrable_toReal_of_lintegral_ne_top performs the final exact real/ENNReal bridge.
-- source:
--   Pinned Mathlib Measurable.lintegral_prod_right and integrable_toReal_of_lintegral_ne_top, plus gaussian_esscher_double_tail_global_mass_finite.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_esscher_kernel_toReal_integrable
    (μ : Measure ℝ) [SFinite μ]
    (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    Integrable (fun t : ℝ =>
      (∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) *
            ENNReal.ofReal (Real.exp (-(φ * z)))
         else 0) ∂μ).toReal) volume := by sorry
