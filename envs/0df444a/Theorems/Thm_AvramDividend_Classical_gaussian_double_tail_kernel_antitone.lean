-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_antitone
-- name    : AvramDividend.Classical.gaussian_double_tail_kernel_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:00:48.166007+00:00
-- url     : https://prove2.me/theorems/2324a11e-2324-476b-bb4b-db36e39a77ca
-- title:
--   Positive-time antitonicity of the Gaussian Esscher double-tail kernel
-- statement:
--   Integrating the already Proved scalar pointwise antitonicity of the double-tail jump atom gives that the Gaussian Esscher double-tail kernel decreases as positive time increases. This applies to arbitrary measures and extended nonnegative integrals, making it suitable for the zero/infinite small-jump variation regimes. Combined with a.e. kernel finiteness, it supports all-positive-time finiteness and the Volterra regularity argument.
-- source:
--   Requires Proved gaussian_double_tail_atom_antitone; pinned lintegral_mono.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_kernel_antitone (μ : Measure ℝ) (φ s t : ℝ)
    (hs : 0 < s) (hst : s ≤ t) :
    (∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) ≤
    (∫⁻ z : ℝ,
      (if 0 < s ∧ s < z then
        ENNReal.ofReal (z - s) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) := by sorry
