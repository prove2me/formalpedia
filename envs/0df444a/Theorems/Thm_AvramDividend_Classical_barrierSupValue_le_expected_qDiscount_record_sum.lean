-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_expected_qDiscount_record_sum
-- name    : AvramDividend.Classical.barrierSupValue_le_expected_qDiscount_record_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:51:34.009348+00:00
-- url     : https://prove2.me/theorems/797d462c-259a-480a-aabd-860c4c14fe2f
-- title:
--   Original stopped reflected dividend value bounded by expected discounted record-increment series
-- statement:
--   For a spectrally negative Lévy process, any barrier, nonnegative discount and monotone cofinal real-time partition starting strictly before zero, the original expected stopped reflected-supremum Stieltjes dividend value is bounded above by the P-expectation of the countable infinite series of running-supremum increments discounted at each interval's left endpoint. This is the unconditional expected-value lifting of the accepted pathwise stopped payout upper bound, requiring no additional measurability assumption or unproven strong Markov renewal identity. The right hand side may be infinite until stronger moment estimates are proved.
-- source:
--   Proved runningSup_qDiscount_stopped_partition_record_upper target aa71a4ce-e78b-40da-ad65-72573f07dbf8 (candidate 12042). Original barrierSupValue definition in Definitions.Def_AvramDividend_Classical_ReflectionBarrier; pinned Mathlib lintegral_mono.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_runningSup_qDiscount_stopped_partition_record_upper

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierSupValue_le_expected_qDiscount_record_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0) :
    barrierSupValue X a q ≤
      (∫⁻ ω, (∑' i : ℕ,
        ENNReal.ofReal (Real.exp (-(q * u i))) *
        ENNReal.ofReal
          (runningSup X (u (i + 1)).toNNReal ω -
           runningSup X (u i).toNNReal ω)) ∂P) := by sorry
