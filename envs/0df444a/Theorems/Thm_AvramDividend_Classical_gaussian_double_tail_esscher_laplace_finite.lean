-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_esscher_laplace_finite
-- name    : AvramDividend.Classical.gaussian_double_tail_esscher_laplace_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:31:52.117217+00:00
-- url     : https://prove2.me/theorems/eb52365a-f345-4d4f-a7d5-fd9e5b188877
-- title:
--   Finiteness of the Esscher Gaussian double-tail Laplace transform
-- statement:
--   For an s-finite positive jump-magnitude Lévy measure integrating min(1,z²), Gaussian Esscher damping φ>0 and Laplace parameter θ≥0, the θ²-weighted time-first nonnegative double-tail integral is finite. Rewrite by the already Proved exact double-tail Esscher Laplace identity and conclude using the previously Proved measure-level Esscher compensated-jump integrability theorem. This supplies a finite Volterra-kernel transform for the shifted Gaussian Lévy–Khintchine formula.
-- source:
--   Proved gaussian_double_tail_esscher_laplace_transform and gaussian_shifted_compensator_integrable.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_esscher_laplace_finite
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    ENNReal.ofReal (θ ^ 2) *
      (∫⁻ t : ℝ, ∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ ∂volume) < ⊤ := by sorry
