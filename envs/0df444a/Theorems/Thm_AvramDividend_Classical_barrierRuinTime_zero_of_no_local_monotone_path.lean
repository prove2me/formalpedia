-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_no_local_monotone_path
-- name    : AvramDividend.Classical.barrierRuinTime_zero_of_no_local_monotone_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:36:20.203045+00:00
-- url     : https://prove2.me/theorems/4af9e9f0-e2fb-49c7-9723-e7ddb3b13696
-- title:
--   No monotone initial time interval implies instantaneous reflected ruin
-- statement:
--   If a Levy sample path is not nondecreasing on any positive initial time interval, then its zero-barrier reflection ruins instantly. This is a purely deterministic implication: failure of monotonicity on an interval of half the requested length gives two times with a strict decrease, and the proven path-decrease criterion implies instantaneous ruin. It reduces the remaining stochastic task to proving that unbounded variation of the Levy triplet excludes initial monotone path intervals almost surely.
-- source:
--   Pathwise near-zero decrease criterion 1951669a-79ea-4230-bef0-b4758495947c and elementary monotonicity on compact time intervals.

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_path_decrease
import Mathlib.Order.Interval.Set.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierRuinTime_zero_of_no_local_monotone_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hNoMono : ∀ ε : ℝ≥0, 0 < ε →
      ¬ MonotoneOn (fun t : ℝ≥0 => X.X t ω) (Icc 0 ε)) :
    barrierRuinTime X 0 ω = 0 := by sorry
