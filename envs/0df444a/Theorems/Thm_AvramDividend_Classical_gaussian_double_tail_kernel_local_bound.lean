-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_local_bound
-- name    : AvramDividend.Classical.gaussian_double_tail_kernel_local_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T20:37:57.358744+00:00
-- url     : https://prove2.me/theorems/7a73bd5d-6824-4159-a132-d7aea6ff384b
-- title:
--   Uniform finite bound for Gaussian Esscher double-tail kernels at positive times
-- statement:
--   For any delta greater than zero, all time arguments t at least delta have Esscher Gaussian double-tail kernel bounded by its finite value at delta. This local positive-time domination follows from proved kernel antitonicity and pointwise finiteness and prepares dominated-convergence regularity steps.
-- source:
--   Consequences of Proved gaussian_double_tail_kernel_antitone and gaussian_double_tail_kernel_finite_positive.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_kernel_local_bound
    (μ : Measure ℝ) [SFinite μ] (φ δ t : ℝ)
    (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (hδ : 0 < δ) (hδt : δ ≤ t) :
    (∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) ≤
    (∫⁻ z : ℝ,
      (if 0 < δ ∧ δ < z then
        ENNReal.ofReal (z - δ) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) ∧
    (∫⁻ z : ℝ,
      (if 0 < δ ∧ δ < z then
        ENNReal.ofReal (z - δ) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) < ⊤ := by sorry
