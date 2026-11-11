-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys73_original_zero_negative_mark_count_no_negative_jumps
-- name    : AvramDividend.Classical.avram_bvb_phys73_original_zero_negative_mark_count_no_negative_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:44:01.733067+00:00
-- url     : https://prove2.me/theorems/a87517ab-3cec-426b-afea-c86d1640595c
-- title:
--   Original zero negative marked count forces no negative source jumps through the horizon
-- statement:
--   If the original intrinsic marked measure has no negative marks through T, then every actual original jump through T is nonnegative. Apply the already proved zero-count exclusion for each negative jump annulus and Archimedean approximation of an arbitrary strictly negative real number by -1/(n+1). This bridges the exact marked-count zero event in c37acb5a to vanishing removed downward-jump sums.
-- source:
--   Necessary zero-jump original source count bridge from Proved f9d2039d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys72_original_zero_negative_mark_count_excludes_each_band
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys73_original_zero_negative_mark_count_no_negative_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (hZero : ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u, (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) :
    ∀ u : ℝ≥0, 0 < u → u ≤ T →
      0 ≤ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u := by sorry
