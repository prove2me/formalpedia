-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_arbitrary_mark_adjacent_interval_additive
-- name    : AvramDividend.Classical.avram_wave7_01_original_intrinsic_arbitrary_mark_adjacent_interval_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:25:03.07796+00:00
-- url     : https://prove2.me/theorems/04cf48c4-85ab-4976-b73d-e09b5932144b
-- title:
--   Original Lévy intrinsic jump counts add across adjacent intervals for arbitrary Borel marks
-- statement:
--   For every original Lévy sample ω and all three ordered times s≤t≤u, the actual intrinsic marked count on (s,u]×B equals the sum on (s,t]×B and (t,u]×B for arbitrary Borel mark B. The equality is pathwise for the canonical Ω,X and needs no finite-activity assumption, moment assumptions, alternate model or conditional intensity premise.
-- source:
--   The original intrinsic marked count is a measure on time–mark pairs. Partition the interval product into disjoint adjacent Borel rectangles and use measure_union. Extends the narrower finite-band zero-start additivity interface to arbitrary Borel marks and general time endpoints.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_intrinsic_arbitrary_mark_adjacent_interval_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v,
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
     NX (Ioc s u ×ˢ B) =
       NX (Ioc s t ×ˢ B) + NX (Ioc t u ×ˢ B)) := by sorry
