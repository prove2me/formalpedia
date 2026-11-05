-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_window_count_finset_filter
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_window_count_finset_filter
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:22:43.562005+00:00
-- url     : https://prove2.me/theorems/0d0d4845-db61-4898-a90b-203670fe6ee1
-- title:
--   Original negative-band window count is the filtered finite source jump-time cardinal
-- statement:
--   For the original process and negative mark band, the jump count in any half-open physical interval contained in (0,T] equals the filter cardinal of the actual finite full-horizon marked jump times.
-- source:
--   Exact accepted original interval count theorem 155906d4 and original finite marked-time theorem e5e6f70b, pinned Mathlib 0df444a; a deterministic finite-set intersection/filter identity with s<=t<=T.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_interval_negative_band_count_ncard

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_window_count_finset_filter
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (n : ℕ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
    (((avram_wave7_06_original_negative_band_marked_times_finite
      X ω T n).toFinset.filter (fun u => s < u ∧ u ≤ t)).card : ℝ≥0∞) := by sorry
