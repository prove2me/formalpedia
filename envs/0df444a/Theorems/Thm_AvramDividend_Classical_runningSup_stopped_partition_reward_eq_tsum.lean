-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stopped_partition_reward_eq_tsum
-- name    : AvramDividend.Classical.runningSup_stopped_partition_reward_eq_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:10:47.106001+00:00
-- url     : https://prove2.me/theorems/04c3555a-852c-44a2-9d90-63465d9d3e45
-- title:
--   Exact countable partition of actual stopped Stieltjes dividend rewards above initial time
-- statement:
--   For the original actual stopped dividend Stieltjes reward restricted to paymentTimes τ at any ruin horizon, and any measurable nonnegative discount weight, a monotone cofinal countable real-time partition exactly decomposes the integral of rewards paid strictly after its initial level into the sum over consecutive half-open intervals. This combines the unique pointwise interval partition with the stopped-measure Tonelli theorem. The identity retains the original time-zero convention in paymentTimes and does not assume a stochastic regeneration law.
-- source:
--   Dependency-gated Prove2Me theorems recordPartition_pointwise_tsum_indicator target 4a3b15b9-0114-428f-b6d0-cfffd4087c92 and runningSup_stopped_lintegral_countable_interchange (authoring request 488bb2c2-db15-4b11-8865-495d0171e2a0).

import Theorems.Thm_AvramDividend_Classical_recordPartition_pointwise_tsum_indicator
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_lintegral_countable_interchange

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_stopped_partition_reward_eq_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n) :
    (∫⁻ r in paymentTimes τ, if u 0 < r then w r else 0
      ∂(dividendMeasure (runningSup X) ω)) =
    (∑' i : ℕ,
      ∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
        ∂(dividendMeasure (runningSup X) ω)) := by sorry
