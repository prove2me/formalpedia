-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_source14_original_zero_prejump_negative_mark_subsingleton
-- name    : AvramDividend.Classical.avram_bv_source14_original_zero_prejump_negative_mark_subsingleton
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:22:36.519002+00:00
-- url     : https://prove2.me/theorems/ee264adb-f0dc-409b-8fe6-a93ba778d7f0
-- title:
--   At most one original negative jump from zero prepayment reserve occurs before or at ruin
-- statement:
--   For the actual spectrally negative Levy driver and any dividend process D, among times at or before the original ruin clock when the prepayment reserve built from the driver's left limit is exactly zero, at most one time can feature a strictly negative driver jump. Such a jump makes the prepayment risk negative, so its time must equal ruin. This is the pathwise count bound needed for original stopped zero-occupation compensation; identifying the predictable zero mask with this prepayment reserve is a separate obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_source14_original_zero_prejump_negative_mark_subsingleton
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Set.Subsingleton {t : ℝ≥0 |
      (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω = 0 ∧
      X.X t ω < Function.leftLim (fun s : ℝ≥0 => X.X s ω) t} := by sorry
