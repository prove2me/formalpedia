-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_map_shift_of_support
-- name    : AvramDividend.Classical.barrierStrategy_dividendMeasure_map_shift_of_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:51:19.809312+00:00
-- url     : https://prove2.me/theorems/3093890e-4ed7-4198-8491-5f41d268763c
-- title:
--   Whole barrier Stieltjes dividend measure translates to post-upcrossing reflected increments
-- statement:
--   At a finite first upcrossing of the barrier, the entire pre-ruin-unrestricted Stieltjes payment measure equals the time-translated dividend measure of the shifted post-passage running supremum, provided both measures have zero nonpositive-time mass and the original measure is locally finite. This is a pathwise whole-measure identity required before strong-Markov stopped-payoff factorisation.
-- source:
--   Root-connected bridge for the only Open child 79978d61-9d1f-4b20-b8a5-114797a8e380. Composes Proved first-upcrossing cumulative-mass equality 443876a6-e856-480c-8a37-40deba77bd09, no prepayment 4396ddd6-6981-42c6-9f15-733157b72a22, nonpositive-window support lemma and translated-measure uniqueness 50431279-23d0-42be-b261-421a5476921e. Conditions are explicit for later discharge from Stieltjes real-time extensions.

import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_shifted_runningSup_dividendMeasure_Ioc_unconditional
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_through_firstUpcrossing
import Theorems.Thm_AvramDividend_Classical_measure_Iic_zero_of_zero_nonpositive_and_initial_window
import Theorems.Thm_AvramDividend_Classical_measure_eq_translated_of_zero_prepayment_and_cumulative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_dividendMeasure_map_shift_of_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    [IsLocallyFiniteMeasure (dividendMeasure (barrierStrategy X x a) ω)]
    (hμneg : (dividendMeasure (barrierStrategy X x a) ω)
      (Set.Iic (0 : ℝ)) = 0)
    (hνneg : (dividendMeasure
      (fun r _ =>
        sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
      ω) (Set.Iic (0 : ℝ)) = 0) :
    dividendMeasure (barrierStrategy X x a) ω =
      Measure.map (fun t : ℝ => (u : ℝ) + t)
        (dividendMeasure
          (fun r _ =>
            sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
          ω) := by
  sorry
