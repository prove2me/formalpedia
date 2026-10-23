-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_full_lintegral
-- name    : AvramDividend.Classical.gaussian_double_tail_atom_full_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T12:03:29.392946+00:00
-- url     : https://prove2.me/theorems/25542e3d-2474-454e-8d46-49934e55565d
-- title:
--   Gaussian double-tail atom over all positive times
-- statement:
--   The time-first Gaussian jump kernel integrates to exp(-φz)z²/2 for positive jump magnitude z, with the full real integral restricted by a 0<t<z indicator. Pull the kernel into an Ioo set integral using lintegral_indicator, replace Ioo by Ioc almost everywhere under atomless Lebesgue measure, and reuse the published weighted atom identity.
-- source:
--   lintegral_indicator, Ioo_ae_eq_Ioc, setLIntegral_congr, gaussian_double_tail_weighted_atom_lintegral

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_atom_full_lintegral (φ z : ℝ) (hz : 0 ≤ z) : (∫⁻ t : ℝ, (if 0 < t ∧ t < z then ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂volume) = ENNReal.ofReal (Real.exp (-(φ * z))) * ENNReal.ofReal (z ^ 2 / 2) := by sorry
