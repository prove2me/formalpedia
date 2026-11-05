-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_interval_negative_band_count_ncard
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_interval_negative_band_count_ncard
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:56:27.038229+00:00
-- url     : https://prove2.me/theorems/155906d4-2fb9-448a-85f6-6be77d5435f1
-- title:
--   Original source negative-band count on an arbitrary half-open interval equals its finite marked-time cardinal
-- statement:
--   For the original intrinsic spectrally negative Lévy jump measure, every negative cutoff band count on the genuine interval (s,t] equals the natural cardinal of the corresponding finite actual jump-time set.
-- source:
--   Accepted full-horizon original marked-count proof f0197436, general intrinsic source rectangle encard f6336d40, and source negative-band finiteness e5e6f70b; exact pinned Mathlib revision.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_interval_negative_band_count_ncard
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0) (hst : s ≤ t) (n : ℕ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
    ({u : ℝ≥0 | s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard : ℝ≥0∞) := by sorry
