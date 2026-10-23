-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_weighted_atom_lintegral
-- name    : AvramDividend.Classical.gaussian_double_tail_weighted_atom_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T11:58:56.788719+00:00
-- url     : https://prove2.me/theorems/6e4bb13d-a036-4598-b62f-9ff49c5e5056
-- title:
--   Esscher-weighted triangular kernel atom integral
-- statement:
--   Integrating the triangular jump kernel over positive times and extracting its constant positive Esscher weight yields exp(−φz)z²/2, using the already published and proved unweighted atom lintegral.
-- source:
--   MeasureTheory.lintegral_const_mul; gaussian_double_tail_unweighted_atom_lintegral

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_weighted_atom_lintegral (φ z : ℝ) (hz : 0 ≤ z) : (∫⁻ t in Ioc (0 : ℝ) z, ENNReal.ofReal (Real.exp (-(φ * z))) * ENNReal.ofReal (z - t) ∂volume) = ENNReal.ofReal (Real.exp (-(φ * z))) * ENNReal.ofReal (z ^ 2 / 2) := by sorry
