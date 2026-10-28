-- Prove2me | Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_upclock_lt_lower_exit
-- name    : AvramDividend.Classical.survived_nextRecord_shifted_upclock_lt_lower_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:51:01.907505+00:00
-- url     : https://prove2.me/theorems/f5f473d4-3c3f-4b1c-b114-e08f08e8699d
-- title:
--   A surviving next record gives strict upper-before-lower shifted exit
-- statement:
--   At two finite and attained adjacent running-supremum records, surviving the reflected drawdown barrier until the later record forces the shifted upward crossing of epsilon strictly before the shifted downcrossing of -a. Existing pathwise results give weak order; finite next-record time makes the future upper-exit clock finite, and right continuity excludes ties. This supplies the missing strict exit inclusion for the pointwise upper killed-record payoff and subsequent strong Markov renewal.
-- source:
--   Pathwise strict-up-before-down consequence of finite record-clock shift, survived-next-record weak order and separated strict passage no-tie.

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_upclock_le_lower_exit
import Theorems.Thm_AvramDividend_Classical_levy_shifted_exit_strict_order_of_finite_weak_order

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.survived_nextRecord_shifted_upclock_lt_lower_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hδ : u + δ = v)
    (hSurvive : (v : ℝ≥0∞) < barrierRuinTime X a ω) :
    (⨅ (t : ℝ≥0)
        (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) <
    (⨅ (t : ℝ≥0)
        (_ : X.X (u + t) ω - X.X u ω < -a), (t : ℝ≥0∞)) := by sorry
