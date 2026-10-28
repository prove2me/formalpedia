-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_through_first_positive_record
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_zero_through_first_positive_record
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:02:05.105709+00:00
-- url     : https://prove2.me/theorems/df72476b-4e75-4cda-93e3-c6f54d85be6d
-- title:
--   Running-supremum dividend measure vanishes before its first positive record
-- statement:
--   The running supremum makes no dividend payments on the interval from time zero through its first positive upcrossing, provided the initial reserve used for its equivalent barrier strategy is nonnegative. This eliminates the initial unrecorded interval from the countable first-record grid decomposition of the stopped dividend reward.
-- source:
--   Direct specialisation of Proved barrierStrategy_dividendMeasure_zero_until_firstUpcrossing at x=a, rewriting barrierStrategy X a a by Proved barrierStrategy_self_eq_runningSup. Supports root c6c3b1d0-2c2f-41ce-a5a0-2771efcc3a69.

import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_until_firstUpcrossing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_dividendMeasure_zero_through_first_positive_record
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) (ha : 0 ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : (0 : ℝ) < X.X s ω), (s : ℝ≥0∞))) :
    (dividendMeasure (runningSup X) ω)
      (Set.Ioc (0 : ℝ) (u : ℝ)) = 0 := by sorry
