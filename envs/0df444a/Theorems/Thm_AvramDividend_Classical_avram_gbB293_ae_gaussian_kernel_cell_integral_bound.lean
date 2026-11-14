-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB293_ae_gaussian_kernel_cell_integral_bound
-- name    : AvramDividend.Classical.avram_gbB293_ae_gaussian_kernel_cell_integral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:13:39.106201+00:00
-- url     : https://prove2.me/theorems/5a0ceece-4db9-4248-bf82-9cc997c24c63
-- title:
--   Almost-everywhere inverse square root Gaussian envelope controls a translated physical-cell integral
-- statement:
--   An interval-integrable real time-density bounded almost everywhere by K times inverse square root of elapsed time has physical-cell integral at most 2K sqrt(delta). Use pinned interval integral monotonicity and the Proved B280 kernel identity. The a.e. hypothesis permits null endpoints in original Gaussian good-cell integration.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_gbB293_ae_gaussian_kernel_cell_integral_bound (s δ K : ℝ) (hδ : 0 ≤ δ) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume s (s + δ))
    (hg : IntervalIntegrable
      (fun t : ℝ => (t - s) ^ (-(1 / 2 : ℝ))) volume s (s + δ))
    (hbound : ∀ᵐ t ∂(volume.restrict (Set.Icc s (s + δ))),
      f t ≤ K * (t - s) ^ (-(1 / 2 : ℝ))) :
    (∫ t in s..(s + δ), f t) ≤ 2 * K * Real.sqrt δ := by sorry
