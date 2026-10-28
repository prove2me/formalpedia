-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_preUpcrossingRuin_iff_lowerClockBefore
-- name    : AvramDividend.Classical.barrierStrategy_preUpcrossingRuin_iff_lowerClockBefore
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:06:42.482689+00:00
-- url     : https://prove2.me/theorems/ee923e63-daf3-4e4f-88ad-1d416d921a62
-- title:
--   Controlled ruin before finite upper passage is equivalent to lower first-passage clock earlier
-- statement:
--   For a finite upper first-passage time, existence of ruin under the barrier policy before that time is equivalent to the raw process's extended lower passage clock occurring strictly earlier. Supplies the exact stochastic killing-event correspondence for the dividend value strong-Markov split.
-- source:
--   W-free child 79978d61-9d1f-4b20-b8a5-114797a8e380. Compose event-level negative reserve lemma from publication request 4983c21c-f3e5-4111-9d31-60fc310b9b69 and lower infimum witness lemma from c06e21f0-43e2-4139-87a0-5836f90d48e9, when both Proved.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinBeforeFirstUpcrossing_iff_rawDowncrossing
import Theorems.Thm_AvramDividend_Classical_lowerCrossingClock_lt_horizon_iff_exists_witness

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_preUpcrossingRuin_iff_lowerClockBefore
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    (∃ t : ℝ≥0, t < u ∧
       riskProcess X x (barrierStrategy X x a) t ω < 0) ↔
    (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) <
      (u : ℝ≥0∞) := by
  sorry
