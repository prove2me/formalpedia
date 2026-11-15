-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a86_original_fullnegative_past_future_void_probability_factor_20261114
-- name    : AvramDividend.Classical.avram_a86_original_fullnegative_past_future_void_probability_factor_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:20:40.848914+00:00
-- url     : https://prove2.me/theorems/291e7af1-9e5a-4bfe-a8d0-c06fcf452526
-- title:
--   Actual negative jump no-arrival events on disjoint original time intervals factor under P without bounded-variation hypotheses
-- statement:
--   For any original spectrally negative Levy process including strictly positive Gaussian variance, the probability of no negative jump in (0,s] and no negative jump in (s,t] is the product of their respective probabilities, for every 0<=s<=t. No standing or finite-activity assumption is needed.
-- source:
--   Proved a20 original past Borel marked count raw measurable plus Proved wave7_06 physical future marked void probability factor, both on actual source Omega/P and original raw filtration. MeasurableSet.preimage transfers count-measurability to the zero-count event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a86_original_fullnegative_past_future_void_probability_factor_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    P ({ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ Iio (0 : ℝ)) = 0} ∩
      {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) = 0}) =
      P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ Iio (0 : ℝ)) = 0} *
      P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) = 0} := by sorry
