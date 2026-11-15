-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_transition_kernel_integral_eq_gaussianReal
-- name    : AppliedSDE.SarkkaSolin.gaussian_transition_kernel_integral_eq_gaussianReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:53:56.669683+00:00
-- url     : https://prove2.me/theorems/df2b7e83-6133-4c73-9f18-3eff0b64c60a
-- title:
--   Gaussian transition-kernel integral equals Gaussian probability-law expectation
-- statement:
--   The Gaussian transition-density kernel of drift b over duration h and variance rate q integrates any real test function exactly as the Gaussian probability measure with mean y+b*h and variance q*h. Uses the pinned Mathlib gaussianReal probability density and integration formula, and is a reusable bridge for the delta-initial-data Gaussian Fokker Planck theorem 45882bf3-274d-457a-b807-a8c188685a8d.
-- source:
--   Sarkka and Solin (2019), Gaussian Fokker Planck transition kernel; supporting theorem 45882bf3-274d-457a-b807-a8c188685a8d.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.gaussian_transition_kernel_integral_eq_gaussianReal
    (b q y h : ℝ) (hq : 0 < q) (hh : 0 < h)
    (f : ℝ -> ℝ) :
    let variance : ℝ≥0 := ⟨q * h, (mul_pos hq hh).le⟩
    (∫ x : ℝ,
      (Real.exp (-((x - y - b * h) ^ 2 / (2 * q * h))) /
        Real.sqrt (2 * Real.pi * q * h)) * f x) =
      ∫ x : ℝ, f x ∂(gaussianReal (y + b * h) variance) := by
  sorry
