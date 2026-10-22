-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_levy_large_jump_finite
-- name    : AvramDividend.Classical.gaussian_levy_large_jump_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T13:03:17.187974+00:00
-- url     : https://prove2.me/theorems/0f9cbddb-42d9-4262-96d8-5bfcd5cb83e3
-- title:
--   Finite Lévy intensity of large positive jumps
-- statement:
--   For a positive jump-magnitude Lévy measure satisfying finite integral of min(1,z²) over positive magnitudes, the measure of jumps at least unit magnitude is finite. This is the large-jump part of the finite-annulus covering needed to derive sigma-finiteness of positive-magnitude pushforwards for Gaussian scale-function regularity.
-- source:
--   Lévy truncated-square condition; pinned Mathlib lintegral_mono_set, ae_restrict_mem, min_eq_left.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_levy_large_jump_finite (μ : Measure ℝ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    μ (Ici (1 : ℝ)) < ⊤ := by sorry
