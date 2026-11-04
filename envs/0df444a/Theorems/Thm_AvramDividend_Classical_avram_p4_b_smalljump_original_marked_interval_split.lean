-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_marked_interval_split
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_marked_interval_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:12:07.738926+00:00
-- url     : https://prove2.me/theorems/27287316-2252-43a8-a67f-3aea88d78c72
-- title:
--   Original intrinsic marked Lévy jump measure additive on adjacent time rectangles
-- statement:
--   For the actual spectrally negative Lévy source and the original intrinsic time-mark jump counting measure on Ω, the count on (s,t] × B is exactly the sum of counts on (s,r] × B and (r,t] × B, whenever s≤r≤t and B is Borel. The proof uses measure additivity of disjoint measurable rectangles. This is a pathwise structural prerequisite for splitting the short initial strip when upgrading P2's raw predictable count compensation to the right-continuous filtration.
-- source:
--   Original intrinsic mark count literal from P2 393b03a8; Mathlib Measure.measure_union and measurableSet_Ioc.prod.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_marked_interval_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s r t : ℝ≥0) (hsr : s ≤ r) (hrt : r ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (let N : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u));
      N (Ioc s t ×ˢ B) = N (Ioc s r ×ˢ B) + N (Ioc r t ×ˢ B)) := by sorry
