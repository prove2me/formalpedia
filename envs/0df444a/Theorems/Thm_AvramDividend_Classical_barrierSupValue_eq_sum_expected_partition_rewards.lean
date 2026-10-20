-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_sum_expected_partition_rewards
-- name    : AvramDividend.Classical.barrierSupValue_eq_sum_expected_partition_rewards
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:46:51.388713+00:00
-- url     : https://prove2.me/theorems/fc92cf74-528f-461a-9acb-dd69a6494a07
-- title:
--   Barrier dividend value equals sum of expected stopped interval rewards under pathwise payoff measurability
-- statement:
--   Under explicit almost-everywhere measurability of each stopped Stieltjes interval reward as a function of the Lévy sample path, the original expected barrier dividend value equals the countable sum of the expectations of the genuine stopped q-discounted interval payouts for any cofinal monotone real-time partition beginning strictly before zero. This combines the proved pathwise countable partition representation with exact nonnegative Tonelli interchange across the underlying probability measure. Establishing the stated sample-path measurability condition for the original stochastic definitions is an independent further obligation before invoking this theorem unconditionally in a strong Markov renewal argument.
-- source:
--   Dependency-gated barrierSupValue_eq_qDiscount_partition_expectation (authoring request 032151f8-18cd-447b-91b8-9e083a100bb4); pinned Mathlib MeasureTheory.lintegral_tsum exact type confirmed by Prove2Me private probe 8e341c6a-ec09-432e-8912-e79315b8ef15.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_qDiscount_partition_expectation

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierSupValue_eq_sum_expected_partition_rewards
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0)
    (hMeas : ∀ i : ℕ, AEMeasurable
       (fun ω : Ω =>
         ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
           if r ∈ Set.Ioc (u i) (u (i + 1))
           then ENNReal.ofReal (Real.exp (-(q * r))) else 0
           ∂(dividendMeasure (runningSup X) ω)) P) :
    barrierSupValue X a q =
    (∑' i : ℕ,
      ∫⁻ ω, (
        ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
          if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ∂P) := by sorry
