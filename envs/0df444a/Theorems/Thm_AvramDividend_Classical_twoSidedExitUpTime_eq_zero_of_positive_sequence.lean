-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_of_positive_sequence
-- name    : AvramDividend.Classical.twoSidedExitUpTime_eq_zero_of_positive_sequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:38:19.835826+00:00
-- url     : https://prove2.me/theorems/f20359ce-5460-40b4-8fa2-921f17aca406
-- title:
--   Positive observations tending to time zero force instantaneous strict upper exit
-- statement:
--   If a Lévy path has strictly positive increments at a sequence of nonnegative observation times tending to zero, its canonical strict first-passage clock above level zero is exactly zero. This is the pathwise first-exit consequence of upward regularity required by upper-endpoint scale and discounted exit arguments.
-- source:
--   Proved observed strict upcrossing clock bound and continuity/order-closed convergence lemmas for the ENNReal clock.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_le_observation_of_strict_exceedance
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.ENNReal.Lemmas

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitUpTime_eq_zero_of_positive_sequence
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s : ℕ → ℝ≥0)
    (hs : Tendsto s atTop (nhds 0))
    (hpos : ∀ n : ℕ, 0 < X.X (s n) ω) :
    twoSidedExitUpTime X 0 ω = 0 := by sorry
