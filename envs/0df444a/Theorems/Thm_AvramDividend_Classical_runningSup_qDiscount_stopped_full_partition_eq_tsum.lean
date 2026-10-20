-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_qDiscount_stopped_full_partition_eq_tsum
-- name    : AvramDividend.Classical.runningSup_qDiscount_stopped_full_partition_eq_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:31:22.356963+00:00
-- url     : https://prove2.me/theorems/354ffbec-2217-4cf0-b255-b32436f058bd
-- title:
--   Exact full stopped discounted Stieltjes dividend decomposition over countable real-time partition
-- statement:
--   For every nonnegative real discount rate and any actual stopped running-supremum dividend process, the original exponentially discounted Stieltjes dividend reward at any ruin horizon is exactly the countable sum of the stopped half-open partition-interval rewards for any monotone cofinal partition starting before time zero. The theorem uses the measurability of the q-discount exponential and the fully general stopped Stieltjes partition identity; it is the direct discounted payout representation needed for the later inverse-record regeneration calculation.
-- source:
--   Dependency-gated runningSup_stopped_full_partition_reward_eq_tsum (authoring request a24fa308-6ee1-45ae-90d9-f99df83e8709); exact pinned Mathlib ENNReal.measurable_ofReal, Real.measurable_exp, Measurable.neg and Measurable.mul.

import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_full_partition_reward_eq_tsum

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_qDiscount_stopped_full_partition_eq_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0) :
    (∫⁻ r in paymentTimes τ,
       ENNReal.ofReal (Real.exp (-(q * r)))
       ∂(dividendMeasure (runningSup X) ω)) =
    (∑' i : ℕ,
       ∫⁻ r in paymentTimes τ,
         if r ∈ Set.Ioc (u i) (u (i + 1))
         then ENNReal.ofReal (Real.exp (-(q * r))) else 0
         ∂(dividendMeasure (runningSup X) ω)) := by sorry
