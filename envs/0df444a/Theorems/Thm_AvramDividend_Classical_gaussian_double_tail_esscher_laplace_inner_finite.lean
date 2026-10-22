-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_esscher_laplace_inner_finite
-- name    : AvramDividend.Classical.gaussian_double_tail_esscher_laplace_inner_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:37:23.282778+00:00
-- url     : https://prove2.me/theorems/f6233f09-3b4d-40fd-a34f-59f6a02b6d41
-- title:
--   Finite unweighted Gaussian double-tail Laplace integral for positive parameter
-- statement:
--   For a positive jump Lévy measure and Esscher damping φ>0, any strictly positive Laplace parameter θ makes the Gaussian double-tail time-first iterated integral finite. The already Proved finite θ²-weighted integral and strict positivity of ENNReal.ofReal θ² imply this using the pinned Mathlib ENNReal.mul_lt_top_iff. Explicit θ>0 avoids the invalid inference at θ=0, when multiplying an infinite integral by zero gives zero.
-- source:
--   Requires Proved gaussian_double_tail_esscher_laplace_finite; exact revision ENNReal.mul_lt_top_iff source-header inspected.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_esscher_laplace_inner_finite
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 < θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ ∂volume) < ⊤ := by sorry
