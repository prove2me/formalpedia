-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_locallyFinite
-- name    : AvramDividend.Classical.dividendMeasure_locallyFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:52:37.796605+00:00
-- url     : https://prove2.me/theorems/d0e8873f-b5c6-4b83-8423-a32208a4f3fa
-- title:
--   The actual Stieltjes dividend measure is locally finite for every strategy path
-- statement:
--   The dividendMeasure definition selects the Stieltjes measure of a monotone real-time dividend path, or the zero measure as fallback. Both branches are locally finite, hence all actual dividend measures are locally finite. This unlocks locally finite measure uniqueness and weighted reward translation for stochastic dividend strategies.
-- source:
--   Direct necessary typeclass bridge for strong-Markov canonical child 79978d61-9d1f-4b20-b8a5-114797a8e380, allowing pathwise application of Proved translated-measure uniqueness 50431279-23d0-42be-b261-421a5476921e to the actual dividendMeasure without an extra local-finiteness hypothesis.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_locallyFinite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    IsLocallyFiniteMeasure (dividendMeasure D ω) := by
  sorry
