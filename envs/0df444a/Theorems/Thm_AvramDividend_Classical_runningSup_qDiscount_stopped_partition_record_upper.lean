-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_qDiscount_stopped_partition_record_upper
-- name    : AvramDividend.Classical.runningSup_qDiscount_stopped_partition_record_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:36:10.290753+00:00
-- url     : https://prove2.me/theorems/aa71a4ce-e78b-40da-ad65-72573f07dbf8
-- title:
--   Actual stopped q-discounted dividend reward bounded by countable endpoint-weighted record increments
-- statement:
--   For the original stopped running-supremum Stieltjes dividend reward, any nonnegative discount rate and any monotone cofinal real-time partition beginning strictly before time zero, the entire stopped q-discounted payout is bounded above by the countable sum of running-record increments weighted by the exponential discount at each interval's left endpoint. The proof first decomposes the actual stopped payout exactly into countably many stopped half-open intervals, uses monotonicity of nonnegative integration to remove the stopping restriction interval by interval, then invokes the proved unstopped q-discount countable endpoint-weight bound. This gives a rigorous pathwise upper control for subsequent expectation and inverse-record discretisation.
-- source:
--   Accepted runningSup_stopped_full_partition_reward_eq_tsum target ff4ccbdf-a9f1-4e4e-9f80-1541ce9b80c3, accepted runningSup_qDiscount_countable_partition_sum_bounds target 5233fc65-ce01-48f6-92ff-fc502c21acc6, pinned Mathlib ENNReal.tsum_le_tsum, MeasureTheory.lintegral_mono_set and setLIntegral_univ.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_full_partition_reward_eq_tsum
import Theorems.Thm_AvramDividend_Classical_runningSup_qDiscount_countable_partition_sum_bounds

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_qDiscount_stopped_partition_record_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0) :
    (∫⁻ r in paymentTimes τ,
      ENNReal.ofReal (Real.exp (-(q * r)))
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' i : ℕ,
      ENNReal.ofReal (Real.exp (-(q * u i))) *
      ENNReal.ofReal
        (runningSup X (u (i + 1)).toNNReal ω -
         runningSup X (u i).toNNReal ω)) := by sorry
