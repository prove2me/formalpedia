-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_sum_expected_partition_rewards_unconditional
-- name    : AvramDividend.Classical.barrierSupValue_eq_sum_expected_partition_rewards_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:21:56.034558+00:00
-- url     : https://prove2.me/theorems/75b7f434-0da5-4424-9c14-8d1600a178a5
-- title:
--   Unconditional expected barrier dividend value equals the countable sum of expected stopped interval payouts
-- statement:
--   For the original reflected supremum dividend value, any nonnegative discount rate and a monotone cofinal half-open time partition beginning before zero, the expected stopped Stieltjes payout equals the countable sum of the expected genuine stopped interval payouts, without additional almost-everywhere measurability assumptions. Each stopped interval payout is measurable by the recently verified unconditional s-finite random dividend kernel construction. A measure-theoretic two-restriction commutation identity equates its interval-restricted kernel representation with the payment-times-restricted interval integrand appearing in the previously accepted conditional countable expectation theorem. This provides the fully unconditional expectation/interchange interface needed by the record-level renewal argument.
-- source:
--   Previously accepted barrierSupValue_eq_sum_expected_partition_rewards target fc92cf74-528f-461a-9acb-dd69a6494a07; newly accepted runningSup_stopped_Ioc_reward_measurable target 94887f4f-dbce-44c9-a7c0-2b76b6466ebc candidate 12365; accepted paymentTimes_measurable target 88dafb7f-65e0-4218-8bde-e06dfe88a7a3; staged two-restriction identity request 571e33b9-9c4f-4c2d-870c-299e502588d2.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_lintegral_two_restrictions_commute
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_Ioc_reward_measurable
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_sum_expected_partition_rewards

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierSupValue_eq_sum_expected_partition_rewards_unconditional
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0) :
    barrierSupValue X a q =
    (∑' i : ℕ,
      ∫⁻ ω, (
        ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
          if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ∂P) := by sorry
