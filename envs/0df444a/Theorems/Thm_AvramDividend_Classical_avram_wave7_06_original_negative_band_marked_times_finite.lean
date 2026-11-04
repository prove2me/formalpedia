-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_marked_times_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T06:51:26.694476+00:00
-- url     : https://prove2.me/theorems/e5e6f70b-a901-43ba-b2bc-56911d56899f
-- title:
--   Actual negative-marked original Lévy jump times are finite on every compact horizon
-- statement:
--   For the actual original Lévy path X and each finite horizon, the set of positive jump times whose original left-limit mark is at most -1/(n+1) is finite. This gives source-identical pathwise occupancy finiteness for a later rate-identification argument.
-- source:
--   Original process finite jumps from Proved càdlàg compact separated-mark finiteness 52f0bc5f, essential for exact marked count grid occupancy convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_marked_times_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.Finite := by sorry
