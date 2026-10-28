-- Prove2me | Theorems.Thm_AvramDividend_Classical_shiftedLevy_ruin_threshold_iff_increment_runningSup
-- name    : AvramDividend.Classical.shiftedLevy_ruin_threshold_iff_increment_runningSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:47:44.991365+00:00
-- url     : https://prove2.me/theorems/cf353649-84d0-4555-a8ba-ec762f31ec13
-- title:
--   Shifted reflected-barrier ruin is exactly the future-increment drawdown threshold
-- statement:
--   At a finite time shift u and relative time t, the strict shifted reserve ruin condition written with max(0, sup of original Lévy values after u minus X(u)) is equivalent to the canonical strict drawdown condition a+X(u+t)-X(u) less than the supremum of future Lévy increments. The running supremum of future increments is nonnegative because the future increment at relative zero is zero, and local boundedness lets the two supremum expressions translate by subtraction of X(u). This is a canonical process-path form for the stopped dividend reward functional.
-- source:
--   Proved shiftedSup_increment_eq_sup_sub 78604350, levyPath_bddAbove_Icc c2066587, shiftedLevy_runningSup_nonnegative f63fc137 when accepted. Bridge from ruin clock b3933be6 to the strong-Markov boundary reward.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_shiftedSup_increment_eq_sup_sub
import Theorems.Thm_AvramDividend_Classical_shiftedLevy_runningSup_nonnegative
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.shiftedLevy_ruin_threshold_iff_increment_runningSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a : ℝ) (ω : Ω) (u t : ℝ≥0) :
    (a + (X.X (u + t) ω - X.X u ω) <
      max 0
        (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
          X.X u ω)) ↔
    (a + (X.X (u + t) ω - X.X u ω) <
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω - X.X u ω) ''
        Set.Icc 0 t)) := by sorry
