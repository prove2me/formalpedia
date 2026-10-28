-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_eq_iInf_reciprocal_of_integrable
-- name    : AvramDividend.Classical.barrierSupValue_zero_eq_iInf_reciprocal_of_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:28:52.669361+00:00
-- url     : https://prove2.me/theorems/79afb977-4739-48aa-8d11-f02e5f0eddb7
-- title:
--   Zero-barrier expected discounted reflected dividends are the limit of positive-barrier values
-- statement:
--   Under finite expected stopped dividends at barrier one and finite initial stopped reward on every sample path, the original zero-barrier reflected-supremum dividend value is the infimum of values for reciprocal positive barriers. The proof combines countable zero-ruin-time convergence, pathwise discounted reward continuity, measurable stopped reward kernels and antitone convergence of expected nonnegative dividends.
-- source:
--   Zero-cap boundary verification, stopped-reward and ruin-time continuity theorems already Proved in the mission.

import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_eq_iInf_reciprocal
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
import Theorems.Thm_AvramDividend_Classical_runningSup_discountedReward_antitone_reciprocal
import Theorems.Thm_AvramDividend_Classical_runningSup_discountedReward_iInf_stopped_of_finite
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_full_reward_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierSupValue_zero_eq_iInf_reciprocal_of_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (hfinite : barrierSupValue X 1 q ≠ ⊤)
    (hpath : ∀ ω : Ω,
      (∫⁻ t in paymentTimes (barrierRuinTime X 1 ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (runningSup X) ω)) ≠ ⊤) :
    barrierSupValue X 0 q =
      ⨅ n : ℕ, barrierSupValue X (1 / ((n : ℝ) + 1)) q := by sorry
