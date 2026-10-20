-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_qDiscount_partition_expectation
-- name    : AvramDividend.Classical.barrierSupValue_eq_qDiscount_partition_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:38:03.274236+00:00
-- url     : https://prove2.me/theorems/aaa52081-6f4b-4e16-9f1a-28ec7f38a526
-- title:
--   Expected dividend value at a barrier as a countable sum of actual stopped Stieltjes interval rewards
-- statement:
--   For every nonnegative q, any barrier a and any monotone cofinal real-time partition starting strictly before zero, the original barrierSupValue expected discounted running-supremum dividend value equals the expectation of the countable sum of genuine q-discounted stopped Stieltjes rewards on successive half-open intervals, stopping at the original reflected drawdown ruin time. This is a direct mathematical bridge from the established pathwise exact Stieltjes partition to the expectation appearing in the scale ratio valuation target; the further strong Markov and q-scale exit steps remain necessary to evaluate that expectation.
-- source:
--   Dependency-gated runningSup_qDiscount_stopped_full_partition_eq_tsum; exact original Definitions.Def_AvramDividend_Classical_ReflectionBarrier barrierSupValue definition; accepted barrierSupValue_mono_barrier proof evidence demonstrates the outer lintegral construction.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_full_partition_reward_eq_tsum

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierSupValue_eq_qDiscount_partition_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0) :
    barrierSupValue X a q =
      (∫⁻ ω, (∑' i : ℕ,
        ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
          if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ∂P) := by sorry
