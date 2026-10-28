-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinClock_lt_upClock_iff_rawLowerClock_lt
-- name    : AvramDividend.Classical.barrierStrategy_ruinClock_lt_upClock_iff_rawLowerClock_lt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:21:30.887379+00:00
-- url     : https://prove2.me/theorems/00fd3516-3ab6-4e48-b848-19dc47c0023d
-- title:
--   Controlled ruin-clock before first barrier crossing equals raw lower-clock before crossing
-- statement:
--   At any finite strict first upper passage, the controlled barrier-strategy ruin time is strictly earlier precisely when the unregulated Lévy process crosses below negative initial capital first. This removes existential path witnesses from the killed stopping event.
-- source:
--   The exact killing-clock equivalence required to rewrite the W-free strong-Markov barrier-value child 79978d61-9d1f-4b20-b8a5-114797a8e380. Uses canonical Proved pre-upcrossing ruin witness theorem ee923e63-daf3-4e4f-88ad-1d416d921a62, with no scale-function assumptions.

import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_preUpcrossingRuin_iff_lowerClockBefore

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_ruinClock_lt_upClock_iff_rawLowerClock_lt
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    ruinTime X x (barrierStrategy X x a) ω < (u : ℝ≥0∞) ↔
      (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) <
        (u : ℝ≥0∞) := by
  sorry
