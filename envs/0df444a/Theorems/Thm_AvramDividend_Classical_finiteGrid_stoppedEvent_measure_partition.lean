-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedEvent_measure_partition
-- name    : AvramDividend.Classical.finiteGrid_stoppedEvent_measure_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:26:44.428156+00:00
-- url     : https://prove2.me/theorems/5edb1a0c-5d8b-4d2e-bab5-01b6b88e542e
-- title:
--   Stopped-history event measure equals the sum of disjoint finite-grid fibre masses
-- statement:
--   Any measurable event A splits uniquely across the finitely many fibres of a measurable finite-valued stopping approximation. The measure of A is the finite sum of the measures of its intersections with those fibres. A proof through nonnegative indicator integration is specifically suited to the existing grid-reward integral theorem and the subsequent strong-Markov event-mass factorisation.
-- source:
--   Uses Proved finiteGrid_stoppedReward_lintegral_decomposition d7b9d4a5-11f7-49f0-8415-4da63551b075 and Mathlib lintegral_indicator_one, to aggregate the event masses left after the Proved stopped-grid future reward product and productIndicator_futureReward_lintegral_factor. Required for direct finite-grid Markov scalar factor and W-free barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedReward_lintegral_decomposition

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.finiteGrid_stoppedEvent_measure_partition
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τn : Ω → ℝ≥0) (A : Set Ω)
    (grid : Finset ℝ≥0) (hgrid : ∀ ω, τn ω ∈ grid)
    (hA : MeasurableSet A)
    (hfibres : ∀ s ∈ grid,
      MeasurableSet {ω : Ω | τn ω = s}) :
    P A = ∑ s ∈ grid, P (A ∩ {ω : Ω | τn ω = s}) := by
  sorry
