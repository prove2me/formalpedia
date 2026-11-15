-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_zero_negative_marks_jump_series_zero
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_zero_negative_marks_jump_series_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T01:10:33.407601+00:00
-- url     : https://prove2.me/theorems/9744006f-ecde-405b-96d4-84272b5983c8
-- title:
--   Original stopped BV physical jump series vanishes on no-negative-mark event
-- statement:
--   Under the original pathwise zero-negative-jump marked count on (0,T], the actual Lévy source has no positive jumps and no negative jumps, hence all source jumps vanish. The complete original physical jump-time real tsum up to each t≤T is therefore zero. This is the missing link from already Proved BV drift-remainder zero to an original linear source path on a no-jump event.
-- source:
--   Combine Proved avram_bvb_phys73_original_zero_negative_mark_count_no_negative_jumps with Proved avram_wave4_04a_actual_levy_jumpmark_nonpositive; each time-increment is zero. The actual original indexed physical jump sum vanishes termwise with no truncation or continuity assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys73_original_zero_negative_mark_count_no_negative_jumps
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_zero_negative_marks_jump_series_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (hZero : ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ (X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) :
    ∀ t : ℝ≥0, t ≤ T →
      (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0) = 0 := by sorry
