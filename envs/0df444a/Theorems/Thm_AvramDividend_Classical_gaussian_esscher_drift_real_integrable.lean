-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_drift_real_integrable
-- name    : AvramDividend.Classical.gaussian_esscher_drift_real_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:27:15.443+00:00
-- url     : https://prove2.me/theorems/5cbc0a23-0379-4f44-9bbe-53f1f57c5374
-- title:
--   Real integrability of Gaussian Esscher drift correction
-- statement:
--   For positive Esscher damping and a Lévy jump-magnitude measure with the truncated-square moment, the canonical compensation correction (z 1_{z≤1})−z exp(−φz) is a real Bochner integrable function on positive jumps. Convert the already proved finite ENNReal integral of its absolute value using the exact Mathlib lintegral_ofReal_ne_top_iff_integrable theorem, and remove the absolute value with integrable_norm_iff.
-- source:
--   Proved gaussian_esscher_drift_correction_integrable; pinned lintegral_ofReal_ne_top_iff_integrable, Real.norm_eq_abs, integrable_norm_iff.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_esscher_drift_real_integrable
    (μ : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    IntegrableOn (fun z : ℝ =>
      (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z))
      (Ioi (0 : ℝ)) μ := by sorry
