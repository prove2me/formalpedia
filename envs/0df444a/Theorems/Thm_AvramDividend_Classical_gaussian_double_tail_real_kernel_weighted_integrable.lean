-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_weighted_integrable
-- name    : AvramDividend.Classical.gaussian_double_tail_real_kernel_weighted_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T14:11:40.364787+00:00
-- url     : https://prove2.me/theorems/aaf85c02-87af-44b0-8093-bf5e9d109a8e
-- title:
--   Positive Laplace weights preserve L1 integrability of the Gaussian Esscher double-tail kernel
-- statement:
--   For a positive Esscher root parameter, a nonnegative Laplace parameter and a spectrally negative Lévy jump-size measure satisfying the truncated quadratic moment condition, the real Esscher double-tail kernel remains Lebesgue integrable on positive times after multiplication by exp(-theta t). The global unweighted kernel is integrable by the previously Proved Gaussian double-tail kernel L1 result. The exponential weight lies in (0,1] for theta≥0,t>0, so the integrability follows by measurable domination.
-- source:
--   Independent L1 localisation lemma used in the Volterra-kernel Laplace inversion; no mission milestone is modified.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_integrable
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_real_kernel_weighted_integrable
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(θ * t)) *
        (∫⁻ z : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal (z - t) *
              ENNReal.ofReal (Real.exp (-(φ * z)))
           else 0) ∂μ).toReal)
      (Ioi (0 : ℝ)) volume := by sorry
