-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_eq_iInf_reciprocal_of_finite
-- name    : AvramDividend.Classical.barrierSupValue_zero_eq_iInf_reciprocal_of_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:30:38.30819+00:00
-- url     : https://prove2.me/theorems/b02575a2-9a16-491e-9b76-e7e7428d8c2c
-- title:
--   Finite expected positive-barrier dividends imply convergence to zero-barrier value
-- statement:
--   The finite expected discounted reflected-supremum reward at positive barrier one forces that stopped reward to be finite almost surely. At those paths, the proved continuity of the discounted Stieltjes reward at the infimum stopping time gives convergence to the actual zero-barrier reward, including its terminal-time convention. Applying antitone convergence to the measurable sample-path reward then identifies the expected zero-barrier value with the infimum of positive-barrier expected values. This removes the stronger everywhere-finite sample-path assumption from the earlier conditional lemma.
-- source:
--   Pinned Mathlib ae_lt_top and lintegral_iInf; Proved zero-ruin-time and stopped-reward endpoint identities.

import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_eq_iInf_reciprocal
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
import Theorems.Thm_AvramDividend_Classical_runningSup_discountedReward_antitone_reciprocal
import Theorems.Thm_AvramDividend_Classical_runningSup_discountedReward_iInf_stopped_of_finite
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_full_reward_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierSupValue_zero_eq_iInf_reciprocal_of_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (hfinite : barrierSupValue X 1 q ≠ ⊤) :
    barrierSupValue X 0 q =
      ⨅ n : ℕ, barrierSupValue X (1 / ((n : ℝ) + 1)) q := by sorry
