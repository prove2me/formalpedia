-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_unweighted_atom_lintegral
-- name    : AvramDividend.Classical.gaussian_double_tail_unweighted_atom_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T11:50:59.250223+00:00
-- url     : https://prove2.me/theorems/88831b00-5f81-4f69-a43c-5c9310f703b8
-- title:
--   Lintegral of an unweighted Gaussian double-tail atom
-- statement:
--   For a nonnegative jump magnitude z, the nonnegative Lebesgue interval integral of t↦z−t over (0,z] equals z²/2, expressed as ENNReal.ofReal. This exact area identity is needed to apply Tonelli to the Gaussian Esscher double-tail kernel and then dominate its total mass by the finite damped quadratic jump moment.
-- source:
--   intervalIntegral.integral_of_le, scalar gaussian_double_tail_unweighted_atom_area, MeasureTheory.ofReal_integral_eq_lintegral_ofReal

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_unweighted_atom_lintegral (z : ℝ) (hz : 0 ≤ z) : (∫⁻ t in Ioc (0 : ℝ) z, ENNReal.ofReal (z - t) ∂volume) = ENNReal.ofReal (z ^ 2 / 2) := by sorry
