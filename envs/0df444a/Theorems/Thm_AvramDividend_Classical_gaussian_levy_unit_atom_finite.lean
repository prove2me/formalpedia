-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_levy_unit_atom_finite
-- name    : AvramDividend.Classical.gaussian_levy_unit_atom_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:10:37.086356+00:00
-- url     : https://prove2.me/theorems/4f21272f-82f6-4dc2-b953-f01e13e2b988
-- title:
--   Finite Lévy jump intensity at the unit magnitude
-- statement:
--   A positive jump-magnitude measure satisfying the Lévy truncated-square condition has finite mass at the singleton {1}. The truncated-square integrand equals one there, and the singleton is a subset of the positive half-line. This controls precisely the boundary atom excluded by the mission's open jump truncation and included by the earlier positive-magnitude Gaussian Volterra formula, allowing its drift correction to be integrated as a finite real quantity.
-- source:
--   Lévy truncated-square integral; pinned lintegral_mono_set, singleton indicator and restriction measurability.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_levy_unit_atom_finite (μ : Measure ℝ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    μ ({1} : Set ℝ) < ⊤ := by sorry
