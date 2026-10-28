-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_of_sequence_at_threshold
-- name    : AvramDividend.Classical.twoSidedExitDownTime_eq_zero_of_sequence_at_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:25:52.617984+00:00
-- url     : https://prove2.me/theorems/18de502d-0c30-4b44-8d47-a0bde5c05d2b
-- title:
--   Strict downward crossings approaching time zero force zero exit time at any threshold
-- statement:
--   For an arbitrary level b, if observation times converge to zero and the Lévy path crosses strictly below b at each time, then the downward first passage occurs instantaneously.
-- source:
--   Observed crossing upper bound, continuity of NNReal-to-ENNReal coercion, and closed order under limits.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.ENNReal.Lemmas

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitDownTime_eq_zero_of_sequence_at_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω)
    (s : ℕ → ℝ≥0)
    (hs : Tendsto s atTop (nhds 0))
    (hcross : ∀ n : ℕ, X.X (s n) ω < b) :
    twoSidedExitDownTime X b ω = 0 := by sorry
