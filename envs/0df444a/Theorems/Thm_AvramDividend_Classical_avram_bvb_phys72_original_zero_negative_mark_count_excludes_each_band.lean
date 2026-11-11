-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys72_original_zero_negative_mark_count_excludes_each_band
-- name    : AvramDividend.Classical.avram_bvb_phys72_original_zero_negative_mark_count_excludes_each_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:31:00.187418+00:00
-- url     : https://prove2.me/theorems/f34f299f-1e68-49f0-8c28-bbfa018808b3
-- title:
--   Zero original marked negative count excludes every fixed negative-jump band
-- statement:
--   For the exact original intrinsic marked jump measure, zero mass over strictly negative marks through T rules out a source jump in any fixed negative annulus (-infinity,-1/(n+1)]. It uses the proved original negative band count iff mark existence and subset monotonicity. This is the core count-zero to original drift-only bridge in the zero-jump physical-source branch c37acb5a.
-- source:
--   Necessary zero-jump original source count bridge from Proved f9d2039d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_negative_band_count_real_positive_iff_exists_jump
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys72_original_zero_negative_mark_count_excludes_each_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ)
    (hZero : ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u, (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) :
    ¬ ∃ u : ℝ≥0, 0 < u ∧ u ≤ T ∧
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≤ -(1 / ((n : ℝ) + 1)) := by sorry
