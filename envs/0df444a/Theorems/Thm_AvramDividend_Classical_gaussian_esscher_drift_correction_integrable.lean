-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_drift_correction_integrable
-- name    : AvramDividend.Classical.gaussian_esscher_drift_correction_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:27:58.833763+00:00
-- url     : https://prove2.me/theorems/f6f9fa10-9c36-43ed-bb13-1d11441cfd8e
-- title:
--   Integrability of Lévy Esscher drift correction under the truncated-square condition
-- statement:
--   For a positive jump-magnitude Lévy measure integrating min(1,z²), the Esscher drift correction with unit-truncation k(z)=z for z≤1 and k(z)=0 for z>1 is absolutely integrable. Dominate its absolute value by (φ+1/φ) min(1,z²), using the Gaussian drift truncation envelope. This removes the remaining integrability obstruction in the shifted Lévy–Khintchine exponent after the already proved compensator integrability and exact shift algebra.
-- source:
--   Depends on independently Proved gaussian_esscher_drift_truncation_envelope; bound via ae_restrict_mem, lintegral_mono_ae and lintegral_const_mul.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_esscher_drift_correction_integrable
    (μ : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal
        |(if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)| ∂μ) < ⊤ := by sorry
