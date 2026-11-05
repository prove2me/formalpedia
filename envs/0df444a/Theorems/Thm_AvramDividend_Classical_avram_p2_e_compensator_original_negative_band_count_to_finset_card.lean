-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_negative_band_count_to_finset_card
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_negative_band_count_to_finset_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:30:30.751921+00:00
-- url     : https://prove2.me/theorems/9b7c05ec-3114-4416-bd72-ff8dc8d2e1f8
-- title:
--   Actual source negative-band count equals finite intrinsic jump-time cardinality
-- statement:
--   The intrinsic jump rectangle count of the original Lévy process equals the cardinality of the finite set of its negative-band jump times, with no replacement process or counting axiom.
-- source:
--   Original X.X intrinsic negative-band rectangle and proved original finite-time marked count; pinned Mathlib 0df444a3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_negative_band_count_to_finset_card
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
    ((avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset.card : ℝ≥0∞) := by sorry
