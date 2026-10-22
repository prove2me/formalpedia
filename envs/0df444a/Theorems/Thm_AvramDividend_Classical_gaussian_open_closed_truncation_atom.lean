-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_open_closed_truncation_atom
-- name    : AvramDividend.Classical.gaussian_open_closed_truncation_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:09:55.675988+00:00
-- url     : https://prove2.me/theorems/45b1b74e-89ca-4f9e-9217-57d8fdbabd27
-- title:
--   Exact unit-atom correction between strict and inclusive Lévy truncations
-- statement:
--   For each real jump magnitude, the strict truncation z 1_{z<1} equals the inclusive truncation z 1_{z≤1} minus the indicator of the boundary magnitude z=1. The identity accounts for the possible jump-measure atom at one and is necessary to transport the mission's open-interval negative-jump Lévy–Khintchine exponent into the previously proved positive-magnitude Gaussian Volterra formula with inclusive cutoff.
-- source:
--   Mission laplaceExponent open-interval truncation versus accepted gaussian_levy_esscher_shift_real inclusive truncation.

import Mathlib

theorem AvramDividend.Classical.gaussian_open_closed_truncation_atom (z : ℝ) :
    (if z < 1 then z else 0) =
      (if z ≤ 1 then z else 0) -
        (if z = 1 then (1 : ℝ) else 0) := by sorry
