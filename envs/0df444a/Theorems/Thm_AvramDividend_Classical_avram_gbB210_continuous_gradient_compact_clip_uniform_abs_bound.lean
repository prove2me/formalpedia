-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB210_continuous_gradient_compact_clip_uniform_abs_bound
-- name    : AvramDividend.Classical.avram_gbB210_continuous_gradient_compact_clip_uniform_abs_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:40:23.930825+00:00
-- url     : https://prove2.me/theorems/9da38930-4046-415a-bebd-ed04e97f1992
-- title:
--   A continuously differentiable reward on a compact clipping interval has a globally bounded clipped gradient
-- statement:
--   A derivative continuous on any closed finite real interval admits a finite nonnegative bound that controls both its values inside the clipping interval and the external fallback value one.
-- source:
--   Avram Gaussian B good selected clip physical L2 uniform bounds; simple compactness corollary independent of the stochastic occupation blocker.

import Mathlib
open MeasureTheory Set Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB210_continuous_gradient_compact_clip_uniform_abs_bound
    (w : ℝ → ℝ) (a b : ℝ)
    (hContinuous : ContinuousOn (deriv w) (Icc a b)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ,
      |if y ∈ Icc a b then deriv w y else 1| ≤ B := by sorry
