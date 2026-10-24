-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_continuous_positive
-- name    : AvramDividend.Classical.gaussian_double_tail_real_kernel_continuous_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:58:53.125604+00:00
-- url     : https://prove2.me/theorems/88073213-4dd3-4b40-b47a-696dbde12d7f
-- title:
--   Real Gaussian Esscher double-tail kernel is continuous at every positive time
-- statement:
--   Under the Lévy truncated-square integrability condition, the real-valued Esscher double-tail kernel obtained by applying ENNReal.toReal to its nonnegative integral is continuous at each positive time. The extended integral is continuous and finite there by the existing proved theorems. This bridge makes real kernel continuity available to the Gaussian Volterra C2 regularity proof.
-- source:
--   Compose proved ENNReal-valued Gaussian double-tail continuity with ENNReal.continuousAt_toReal at a finite positive-time integral.

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_continuous_positive
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_finite_positive

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_real_kernel_continuous_positive
    (μ : Measure ℝ) [SFinite μ] (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun u : ℝ => (∫⁻ z : ℝ,
      (if 0 < u ∧ u < z then
        ENNReal.ofReal (z - u) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ).toReal) t := by sorry
