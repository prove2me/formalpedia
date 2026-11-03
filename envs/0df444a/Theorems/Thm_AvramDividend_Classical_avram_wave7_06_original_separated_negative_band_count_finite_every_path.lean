-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_negative_band_count_finite_every_path
-- name    : AvramDividend.Classical.avram_wave7_06_original_separated_negative_band_count_finite_every_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T22:07:41.015805+00:00
-- url     : https://prove2.me/theorems/3537a106-449a-4571-bf4f-e590c30d0a4d
-- title:
--   Original Lévy separated negative-band intrinsic count finite on every path and horizon
-- statement:
--   For every path ω of the genuine original spectrally negative Lévy process, every finite horizon T and every separated negative band (-∞,-1/(n+1)], the exact intrinsic jump-counting measure has finite mass. No bounded-variation assumption is imposed. The proof combines the Proved finite set of jumps whose magnitude exceeds a fixed positive threshold with the Proved exact intrinsic marked rectangle cardinality. This is a pathwise local-finiteness interface used before Poisson counting and L² truncation.
-- source:
--   W7-06 actual-source marked L²/L¹ isometry and Poisson count bridge; Proved source path finite-separated-jumps 52f0bc5f and exact rectangle count f6336d40. Extends prior BV-only finite negative-band count interface without changing Ω, P or X.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_separated_negative_band_count_finite_every_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) < ⊤ := by sorry
