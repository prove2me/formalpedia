-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys80_original_zero_marks_BV_drift_remainder_vanishes
-- name    : AvramDividend.Classical.avram_bvb_phys80_original_zero_marks_BV_drift_remainder_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:34:15.30208+00:00
-- url     : https://prove2.me/theorems/dab9a278-61f6-4adb-8a9f-12ae1324e8b0
-- title:
--   Original zero-negative-mark BV source drift remainder and jump sum both vanish
-- statement:
--   On the original probability space, under standing BV Lévy assumptions, zero physical negative marks through a finite horizon imply that at every time on that horizon the jump-sum J and the drift remainder R(t)=t·drift-X(t)-J(t) both vanish. This kills the extra signed R-increment source appearing in the canonical uniform-grid B term.
-- source:
--   Original BV cash grid 85b63af5; uses Proved phys73 and phys75 and physical jump nonpositivity

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys73_original_zero_negative_mark_count_no_negative_jumps
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys75_original_zero_negative_mark_count_entire_source_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Both the physical jump sum and the BV drift-remainder source vanish
at every time on the original event with zero negative marks. -/

theorem AvramDividend.Classical.avram_bvb_phys80_original_zero_marks_BV_drift_remainder_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) →
      ∀ t : ℝ≥0, t ≤ T →
        (let J : ℝ≥0 → ℝ := fun s =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ s then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         ((t : ℝ) * X.drift - X.X t ω) - J t = 0) := by sorry
