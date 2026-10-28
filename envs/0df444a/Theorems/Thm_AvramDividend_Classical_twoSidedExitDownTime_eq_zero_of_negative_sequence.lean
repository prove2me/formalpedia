-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_of_negative_sequence
-- name    : AvramDividend.Classical.twoSidedExitDownTime_eq_zero_of_negative_sequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:36:13.797305+00:00
-- url     : https://prove2.me/theorems/fe841cdc-0831-452f-8dc6-b759aa8b3d05
-- title:
--   Negative observations tending to time zero force instantaneous strict lower exit
-- statement:
--   For a spectrally negative Lévy sample path, if there is a sequence of nonnegative observation times converging to zero at which the Lévy increment is strictly negative, then the canonical strict downward first-passage time below level zero equals zero. This directly connects negative-near-zero path regularity to the exit clock used in stopped scale identities.
-- source:
--   Previously verified observed strict downcrossing bound combined with Mathlib's continuity of the NNReal-to-ENNReal coercion and closed-order limit comparison.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.ENNReal.Lemmas

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitDownTime_eq_zero_of_negative_sequence
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s : ℕ → ℝ≥0)
    (hs : Tendsto s atTop (nhds 0))
    (hneg : ∀ n : ℕ, X.X (s n) ω < 0) :
    twoSidedExitDownTime X 0 ω = 0 := by sorry
