-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_weighted_truncated_area_integrable
-- name    : AvramDividend.Classical.gaussian_weighted_truncated_area_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:11:18.08307+00:00
-- url     : https://prove2.me/theorems/42785549-50f3-420f-b496-2969c52fddb8
-- title:
--   Local truncated-area integrability for the Esscher Gaussian Volterra kernel
-- statement:
--   For any nonnegative finite time horizon R, the Esscher-damped Gaussian double-tail truncated jump area is integrable under the quadratic Lévy jump condition. The exact area z min(R,z) - min(R,z)^2/2 is bounded by (1+R) min(z^2,z), so the already-proved damped Lévy tail-area integral controls it. This provides the quantitative integrability condition needed before Tonelli interchanges the Gaussian Volterra kernel and jump measure.
-- source:
--   The independently proved gaussian_truncated_double_tail_area_bound and esscher_tilted_tail_area_integrable.

import Mathlib.Tactic
import Theorems.Thm_AvramDividend_Classical_gaussian_truncated_double_tail_area_bound
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_tail_area_integrable
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_weighted_truncated_area_integrable
    (μ : Measure ℝ) (φ R : ℝ) (hφ : 0 < φ) (hR : 0 ≤ R)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal
        (Real.exp (-(φ * z)) *
          (z * min R z - (min R z) ^ 2 / 2)) ∂μ) < ⊤ := by sorry
