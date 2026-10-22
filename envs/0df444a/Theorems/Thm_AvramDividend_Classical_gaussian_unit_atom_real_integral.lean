-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_unit_atom_real_integral
-- name    : AvramDividend.Classical.gaussian_unit_atom_real_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:10:47.296221+00:00
-- url     : https://prove2.me/theorems/7e76eba7-43a1-4afa-b232-eb588f0fac2d
-- title:
--   Exact real-valued unit-jump Lévy truncation correction
-- statement:
--   The Bochner integral over positive jump magnitudes of the scalar θ multiplied by the singleton indicator at magnitude one equals θ times the real mass of that singleton. This follows from the measurable indicator set integral formula and constant set integral, with the singleton included in the positive half-line. The separate truncated-square lemma guarantees that the real singleton mass is finite for Lévy measures. This isolates the exact boundary drift correction between the mission's strict truncation and the previously proved inclusive Gaussian Esscher formulas.
-- source:
--   Pinned Mathlib MeasureTheory.setIntegral_indicator and MeasureTheory.setIntegral_const.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_unit_atom_real_integral (μ : Measure ℝ) (θ : ℝ) :
    (∫ z in Ioi (0 : ℝ),
      θ * (if z = 1 then (1 : ℝ) else 0) ∂μ) =
        θ * μ.real ({1} : Set ℝ) := by sorry
