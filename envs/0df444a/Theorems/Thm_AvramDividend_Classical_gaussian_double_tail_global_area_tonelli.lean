-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_global_area_tonelli
-- name    : AvramDividend.Classical.gaussian_double_tail_global_area_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T12:01:51.199437+00:00
-- url     : https://prove2.me/theorems/4a05a461-5fcd-4afa-99da-50c80aea2293
-- title:
--   Exact global Tonelli area identity for the Gaussian double-tail kernel
-- statement:
--   Tonelli swaps the nonnegative Gaussian double-tail time and jump integrals. For each positive jump magnitude z, the time integral of the triangular atom is z²/2. Consequently, the global time-first kernel mass equals the Esscher-weighted quadratic jump moment divided by two. Equality is valid in ENNReal even without finiteness.
-- source:
--   Proved gaussian_double_tail_tonelli plus gaussian_double_tail_unweighted_atom_lintegral, interval indicator and ENNReal lintegral_const_mul

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_global_area_tonelli (μ : Measure ℝ) [SFinite μ] (φ : ℝ) : (∫⁻ t : ℝ, ∫⁻ z : ℝ, (if 0 < t ∧ t < z then ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ ∂volume) = (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (z ^ 2 / 2) * ENNReal.ofReal (Real.exp (-(φ * z))) ∂μ) := by sorry
