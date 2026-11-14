-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b130_original_negative_bandfree_cell_exact_compensation_drift
-- name    : AvramDividend.Classical.avram_b130_original_negative_bandfree_cell_exact_compensation_drift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:36:35.320591+00:00
-- url     : https://prove2.me/theorems/4731f7ef-c949-45b4-b259-fc997fbd6bc8
-- title:
--   One absent original negative jump band has exactly its signed compensation drift
-- statement:
--   For the original Levy sample path and genuine half-open physical interval (s,t], suppose a specified negative reciprocal cutoff band n contains no actual source jump. The Proved original finite marked-time compensated signed source theorem gives identical finite marked sums at both endpoints. Their difference is the original signed Levy first-moment compensator times physical elapsed time. This weakens the B80 full jumpfree assumption to the exact one-band condition obtained from B110 zero original source count, and supports the B127 conull cutoff-limit step.
-- source:
--   Proved original avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact original compensated negative-band source has only its signed drift where that physical cutoff band contains no jump. -/

theorem AvramDividend.Classical.avram_b130_original_negative_bandfree_cell_exact_compensation_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (s t : ℝ≥0) (hst : s ≤ t) (ω : Ω)
    (hNoBand : ∀ u : ℝ≥0, s < u → u ≤ t →
      ¬ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1)))) :
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω =
      -((t : ℝ) - (s : ℝ)) *
        (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν) := by sorry
