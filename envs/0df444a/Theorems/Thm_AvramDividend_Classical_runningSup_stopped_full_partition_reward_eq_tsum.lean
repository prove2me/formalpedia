-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stopped_full_partition_reward_eq_tsum
-- name    : AvramDividend.Classical.runningSup_stopped_full_partition_reward_eq_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:22:01.97499+00:00
-- url     : https://prove2.me/theorems/ff4ccbdf-a9f1-4e4e-9f80-1541ce9b80c3
-- title:
--   Full actual stopped dividend reward equals sum over cofinal real-time Stieltjes partition
-- statement:
--   For the actual stopped Stieltjes running-supremum dividend measure at any ruin horizon, a measurable nonnegative discount weight and a monotone cofinal real-time partition beginning strictly before zero, the entire original stopped dividend integral is exactly the sum of the corresponding stopped half-open interval integrals. It respects the original time-zero convention and needs no artificial atom assumption: paymentTimes is measurable, and its elements are nonnegative, so all stopped payments are almost everywhere above the negative initial partition level. This supplies the full deterministic countable reward decomposition needed before introducing the random inverse-record stopping clock.
-- source:
--   Dependency-gated runningSup_stopped_partition_reward_eq_tsum target 04c3555a-852c-44a2-9d90-63465d9d3e45; pinned Mathlib ae_restrict_mem, lintegral_congr_ae (exact remote signatures confirmed in job 96b0f52d-d964-49a1-99fe-dab7e2cf1aac); original paymentTimes definition.

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.Set.Insert
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_partition_reward_eq_tsum

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_stopped_full_partition_reward_eq_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0) :
    (∫⁻ r in paymentTimes τ, w r
      ∂(dividendMeasure (runningSup X) ω)) =
    (∑' i : ℕ,
       ∫⁻ r in paymentTimes τ,
         if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
         ∂(dividendMeasure (runningSup X) ω)) := by sorry
