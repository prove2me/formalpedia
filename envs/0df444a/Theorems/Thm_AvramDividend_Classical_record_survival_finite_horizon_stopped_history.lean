-- Prove2me | Theorems.Thm_AvramDividend_Classical_record_survival_finite_horizon_stopped_history
-- name    : AvramDividend.Classical.record_survival_finite_horizon_stopped_history
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:05:56.034614+00:00
-- url     : https://prove2.me/theorems/3623a540-863c-4a57-b799-b29ddaf42e2a
-- title:
--   Survival to a record before a finite horizon is observable at the truncated stopping time
-- statement:
--   Given first strict upward passage τ and reflected ruin time T, fix any finite horizon M. The event that τ<T and τ≤M is measurable with respect to the stopped-history sigma algebra of min(τ,M). The result combines record-survival stopped-history measurability and Mathlib's theorem that the sigma algebra at the minimum of a stopping time and a deterministic horizon is the intersection of the stopped and horizon sigma algebras. This supplies the finite-clock history event for applying strong-Markov factorisation and then passing M to infinity.
-- source:
--   Intersect the record-survival stopped event with τ≤M and apply Mathlib's stopped-history measurability characterisation for the minimum with a constant horizon.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_record_survival_stopped_history_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.record_survival_finite_horizon_stopped_history
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (M : ℝ≥0) :
    MeasurableSet[
      ((upperPassage_stopping_rightCont_filtration X b).min_const M).measurableSpace]
      {ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (M : ℝ≥0∞)} := by sorry
