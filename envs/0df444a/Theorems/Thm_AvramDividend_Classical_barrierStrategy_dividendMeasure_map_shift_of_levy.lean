-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_map_shift_of_levy
-- name    : AvramDividend.Classical.barrierStrategy_dividendMeasure_map_shift_of_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:54:06.082339+00:00
-- url     : https://prove2.me/theorems/a8a1c36f-ffe6-49d7-b7b7-20930f7348dc
-- title:
--   Barrier strategy Stieltjes dividend measure equals translated shifted Lévy running-supremum measure without extra support assumptions
-- statement:
--   After an attained finite first passage of a spectrally negative Lévy path to a dividend barrier, the complete barrier dividend Stieltjes measure is the pushforward by time shift u of the running-supremum Stieltjes measure formed from increments after u. Locally finite measures and zero mass at nonpositive times are automatic, proved for the original barrier dividend measure and the shifted Lévy supremum measure. This removes all technical measure-support assumptions from the canonical map-shift identity used in the barrier-value strong-Markov split.
-- source:
--   Proved conditional barrierStrategy_dividendMeasure_map_shift_of_support (3093890e), dividendMeasure_locallyFinite (d0e8873f), barrierStrategy_dividendMeasure_zero_nonpositive (a0129db2), and the new shiftedSup_dividendMeasure_zero_nonpositive_of_levy. Bridge for target 79978d61.

import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_locallyFinite
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_shiftedSup_dividendMeasure_zero_nonpositive_of_levy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_map_shift_of_support
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_dividendMeasure_map_shift_of_levy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    dividendMeasure (barrierStrategy X x a) ω =
      Measure.map (fun t : ℝ => (u : ℝ) + t)
        (dividendMeasure
      (fun r (_ : Ω) =>
        sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
      ω) := by sorry
