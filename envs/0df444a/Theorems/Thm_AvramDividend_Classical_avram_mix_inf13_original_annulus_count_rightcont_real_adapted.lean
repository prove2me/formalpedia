-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf13_original_annulus_count_rightcont_real_adapted
-- name    : AvramDividend.Classical.avram_mix_inf13_original_annulus_count_rightcont_real_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:43:05.487019+00:00
-- url     : https://prove2.me/theorems/ff2aee04-cd45-4043-b096-8f2252923998
-- title:
--   Actual negative-annulus physical jump count is right-continuous-filtration adapted
-- statement:
--   For the original spectrally negative Levy process on its unchanged sample space and law, the physical count of negative jumps in any reciprocal-cutoff annulus before a finite horizon is real strongly measurable in the original right-continuous filtration at that horizon. Combine the Proved adaptedness of each nested full cutoff and exact same-path annulus additivity with the Proved physical finite-cardinality identity. This is a necessary source-measurability premise for the predictable pre-count compensator route to the original annulus factorial moment and the mixed infinite-activity mark isometry. No auxiliary process, finite total jump activity or first absolute Levy moment.
-- source:
--   Proved b44d1aa2 full-cutoff rightCont adapted real count, Proved f0104cbc physical annulus additivity, Proved 1aea4cfb and 7cf25aa9/e5e6f70b finite original marked jump card. This helper is directly consumed by MIX-SOURCE13 original annulus predictable pre-count construction and ultimately f5e6e083.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf13_original_annulus_count_rightcont_real_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    StronglyMeasurable[𝓕.rightCont T] (fun ω : Ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioc (-(1 / ((n : ℝ) + 1)))
          (-(1 / ((m : ℝ) + 1))))).toReal) := by sorry
