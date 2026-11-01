-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_positive_square_energy_threshold_finite_mark_intensity
-- name    : AvramDividend.Classical.avram_wave4_p1_positive_square_energy_threshold_finite_mark_intensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:21:24.85221+00:00
-- url     : https://prove2.me/theorems/401645c2-49a2-4ceb-8311-1c3842a5bb0e
-- title:
--   Positive quadratic jump-energy threshold forces finite-rate Lévy mark bands
-- statement:
--   An intensity ν with finite nonnegative g-energy assigns finite mass to every measurable band where g is bounded below by any strictly positive threshold. In Lévy small-jump work, take g(z)=|z|² and B={ε≤|z|≤1}, so each band away from zero is genuinely finite-rate even when ν has infinite activity near 0. This discharges the finite-band measurability/intensity premise required by P1 compensator approximation without using ∫|z|ν or assuming a compensation conclusion.
-- source:
--   Pinned Mathlib MeasureTheory.setLIntegral_const, setLIntegral_mono, setLIntegral_le_lintegral, ENNReal.lt_top_of_mul_ne_top_right.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_positive_square_energy_threshold_finite_mark_intensity
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (g : E → ℝ≥0∞) (hg : Measurable g)
    (henergy : ∫⁻ z, g z ∂ν < ∞)
    (B : Set E) (hB : MeasurableSet B)
    (ε : ℝ≥0∞) (hε : 0 < ε)
    (hthreshold : ∀ z ∈ B, ε ≤ g z) :
    ν B < ∞ := by sorry
