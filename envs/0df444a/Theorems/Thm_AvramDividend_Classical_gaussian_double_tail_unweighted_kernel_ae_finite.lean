-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_unweighted_kernel_ae_finite
-- name    : AvramDividend.Classical.gaussian_double_tail_unweighted_kernel_ae_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:54:09.252849+00:00
-- url     : https://prove2.me/theorems/ccda82bc-00bd-44ee-8545-384ac7296eaf
-- title:
--   Almost-everywhere finite unweighted Esscher double-tail kernel
-- statement:
--   For any positive jump-magnitude Lévy measure satisfying the usual truncated-square integrability and Esscher damping φ>0, the underlying, unweighted Gaussian double-tail Rφ(t)=∫_{z>t}(z−t)e^{-φz} μ(dz) is finite for almost every real time t. Use the already Proved weighted-kernel a.e. finiteness at θ=1, the exact time-weight atom factorisation, measurable-lintegral constant multiplication and positivity of e^{-t} with ENNReal.mul_lt_top_iff.
-- source:
--   Requires Proved gaussian_double_tail_kernel_ae_finite and gaussian_double_tail_time_weight_factor.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_unweighted_kernel_ae_finite
    (μ : Measure ℝ) [SFinite μ] (φ : ℝ)
    (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    ∀ᵐ t : ℝ ∂volume,
      (∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ) < ⊤ := by sorry
