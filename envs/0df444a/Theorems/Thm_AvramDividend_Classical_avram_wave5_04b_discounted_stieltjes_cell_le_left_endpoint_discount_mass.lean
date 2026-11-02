-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_discounted_stieltjes_cell_le_left_endpoint_discount_mass
-- name    : AvramDividend.Classical.avram_wave5_04b_discounted_stieltjes_cell_le_left_endpoint_discount_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:18:52.400521+00:00
-- url     : https://prove2.me/theorems/00b4947d-7c3c-4de6-9058-20912eb4c747
-- title:
--   Exact left-discount envelope for complete Stieltjes mass in a half-open cell
-- statement:
--   For any measure on real time, nonnegative discount rate q and half-open interval (a,b], the lower integral of exp(-q s) against the measure is bounded by exp(-q a) times its full measure on that interval. No assumption of atomicity, absolute continuity or finiteness is needed; singular continuous variation is included. This is the discount envelope required to multiply the closed-cap Stieltjes cell secant by a time-local weight.
-- source:
--   Pinned Mathlib lintegral_mono_ae, ae_restrict_mem for measurable Ioc, Real.exp monotonicity, ENNReal.ofReal_le_ofReal and MeasureTheory.lintegral_const. This is a sharpened shifted counterpart of Proved discounted_stieltjes_lintegral_le_measure fc69051f-30bb-4e32-8f98-3ca0751d60fe.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave5_04b_discounted_stieltjes_cell_le_left_endpoint_discount_mass
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (a b : ℝ) :
    (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(q * a))) * μ (Ioc a b) := by sorry
