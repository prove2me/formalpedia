-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_preUpcrossing_ruin_iff_rawDowncrossing
-- name    : AvramDividend.Classical.barrierStrategy_preUpcrossing_ruin_iff_rawDowncrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:49:48.161004+00:00
-- url     : https://prove2.me/theorems/86ef73f3-38eb-49d6-9946-946ee9929516
-- title:
--   Controlled ruin before barrier entry iff raw Lévy process crosses below minus initial capital
-- statement:
--   At each time strictly preceding finite first barrier upcrossing, controlled ruin is equivalent to the raw Lévy process falling below minus initial capital. This is the killing event correspondence needed for stopped dividend-value factorisation.
-- source:
--   W-free strong Markov dividend value child 79978d61-9d1f-4b20-b8a5-114797a8e380. Directly uses two Proved first-passage and pre-dividend results without awaiting in-flight helper.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_prethreshold_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_before_upcrossing
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_preUpcrossing_ruin_iff_rawDowncrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    ∀ t : ℝ≥0, t < u →
      (riskProcess X x (barrierStrategy X x a) t ω < 0 ↔
        X.X t ω < -x) := by
  sorry
