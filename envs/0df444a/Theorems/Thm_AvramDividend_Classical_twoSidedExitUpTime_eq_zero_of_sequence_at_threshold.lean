-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_of_sequence_at_threshold
-- name    : AvramDividend.Classical.twoSidedExitUpTime_eq_zero_of_sequence_at_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:25:57.302375+00:00
-- url     : https://prove2.me/theorems/b2186ad3-760c-4c65-a0ea-879fb7b1b8a6
-- title:
--   Strict upward crossings approaching time zero force zero exit time at any threshold
-- statement:
--   For an arbitrary level b, if observation times converge to zero and the Lévy path crosses strictly above b at each time, then the upward first passage occurs instantaneously.
-- source:
--   Observed crossing upper bound, continuity of NNReal-to-ENNReal coercion, and closed order under limits.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_le_observation_of_strict_exceedance
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.ENNReal.Lemmas

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitUpTime_eq_zero_of_sequence_at_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω)
    (s : ℕ → ℝ≥0)
    (hs : Tendsto s atTop (nhds 0))
    (hcross : ∀ n : ℕ, b < X.X (s n) ω) :
    twoSidedExitUpTime X b ω = 0 := by sorry
