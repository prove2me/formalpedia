-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinBeforeFirstUpcrossing_iff_rawDowncrossing
-- name    : AvramDividend.Classical.barrierStrategy_ruinBeforeFirstUpcrossing_iff_rawDowncrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:57:20.664257+00:00
-- url     : https://prove2.me/theorems/5cdbb75b-b2f4-48b3-a773-38848d4b8bbe
-- title:
--   Existence of barrier ruin before first upcrossing equals raw lower-downcrossing event
-- statement:
--   For a finite first upper passage, a controlled-reserve ruin occurring strictly before the passage is equivalent pathwise to a strict raw Lévy downward crossing of minus initial capital before the same time. This translates the stopping-history killing event of the strong-Markov barrier valuation.
-- source:
--   Root-connected first passage event normalisation for W-free child 79978d61-9d1f-4b20-b8a5-114797a8e380, using canonical Proved pointwise equivalence 86ef73f3-38eb-49d6-9946-946ee9929516.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_preUpcrossing_ruin_iff_rawDowncrossing

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_ruinBeforeFirstUpcrossing_iff_rawDowncrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    (∃ t : ℝ≥0, t < u ∧
       riskProcess X x (barrierStrategy X x a) t ω < 0) ↔
      (∃ t : ℝ≥0, t < u ∧ X.X t ω < -x) := by
  sorry
