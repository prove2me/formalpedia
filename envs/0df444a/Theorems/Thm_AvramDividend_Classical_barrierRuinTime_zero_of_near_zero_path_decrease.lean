-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_path_decrease
-- name    : AvramDividend.Classical.barrierRuinTime_zero_of_near_zero_path_decrease
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:31:31.187201+00:00
-- url     : https://prove2.me/theorems/1951669a-79ea-4230-bef0-b4758495947c
-- title:
--   Arbitrarily early path decreases imply immediate zero-barrier reflected ruin
-- statement:
--   For a spectrally negative Levy sample path, if there are pairs of times arbitrarily near zero at which the path strictly decreases, then the reflected drawdown crosses the zero barrier arbitrarily soon, so its ruin time is zero. The condition allows both path values to remain positive. This sharpens the previously proved sufficient condition that the path itself must become negative near zero, and is a pathwise bridge towards deriving immediate reflected ruin from unbounded sample-path variation.
-- source:
--   Canonically Proved running supremum monotonicity and domination 848fbd48-f69f-46b9-b2bf-436cb33918a8, and near-zero drawdown ruin criterion 1fa70426-22a7-4003-98e1-939fdb2b0ae4.

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_drawdown
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierRuinTime_zero_of_near_zero_path_decrease
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hDecrease : ∀ ε : ℝ≥0, 0 < ε →
      ∃ s t : ℝ≥0, s ≤ t ∧ t < ε ∧ X.X t ω < X.X s ω) :
    barrierRuinTime X 0 ω = 0 := by sorry
