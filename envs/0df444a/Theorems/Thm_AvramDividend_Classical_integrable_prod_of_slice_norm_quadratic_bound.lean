-- Prove2me | Theorems.Thm_AvramDividend_Classical_integrable_prod_of_slice_norm_quadratic_bound
-- name    : AvramDividend.Classical.integrable_prod_of_slice_norm_quadratic_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:14:31.606741+00:00
-- url     : https://prove2.me/theorems/2552153f-1c61-4917-9e73-4baea9c8ae60
-- title:
--   Product integrability from quadratic control of jump-indexed state slices
-- statement:
--   Let f(x,y) be jointly measurable on a product measure. If for almost every y the x-slice is integrable, the map y→∫|f(x,y)|dx is a.e. strongly measurable, and this slice norm is bounded by C min(1,y²), then f is integrable on the product measure whenever min(1,y²) is ν-integrable. This Fubini criterion accommodates origin-crossing boundary layers for which pointwise factorised state bounds may fail.
-- source:
--   Pinned Mathlib integrable_prod_iff' and domination, to handle the discounted Lévy generator boundary layer.

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem integrable_prod_of_slice_norm_quadratic_bound
    (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (f : ℝ × ℝ → ℝ) (C : ℝ)
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hsections : ∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ)
    (hnorm_meas : AEStronglyMeasurable
      (fun y => ∫ x, ‖f (x, y)‖ ∂μ) ν)
    (hmin : Integrable (fun y : ℝ => min 1 (y ^ 2)) ν)
    (hdom : ∀ᵐ y ∂ν,
      (∫ x, ‖f (x, y)‖ ∂μ) ≤ C * min 1 (y ^ 2)) :
    Integrable f (μ.prod ν) := by sorry

end AvramDividend.Classical
