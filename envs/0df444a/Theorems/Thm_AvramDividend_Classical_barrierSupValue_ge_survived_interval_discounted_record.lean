-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_survived_interval_discounted_record
-- name    : AvramDividend.Classical.barrierSupValue_ge_survived_interval_discounted_record
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T19:42:20.928773+00:00
-- url     : https://prove2.me/theorems/0bd09690-1e02-4cbb-a4a8-073427d7b596
-- title:
--   Original expected barrier dividends dominate the discount-weighted record increment from an interval surviving reflected ruin
-- statement:
--   For any actual spectrally negative Lévy reflected-dividend policy and any deterministic time interval (s,t] beginning at nonnegative s, the original complete expected discounted dividend value at barrier a dominates the expected realised record increment over that interval, discounted at terminal time t and restricted to sample paths on which t strictly precedes the actual reflected-drawdown ruin time. This is an unconditional lower bound on the genuine barrier value in terms of record growth on surviving paths. It uses the proved exact full-horizon reward indicator representation, the proved fully-surviving-interval Stieltjes lower bound and the accepted inclusion of (s,t] in paymentTimes on terminal survival. No independent-increment, strong Markov or ordinary scale-exit hypotheses are introduced.
-- source:
--   Accepted barrierSupValue_eq_full_reward_indicator_expectation target fe6aa85a-6f7b-4dfc-820f-785a6c9b9f0b candidate 12376; accepted stopped interval two-sided bound target 7d59aefb-31f3-40d2-85e0-b0477c351129 candidate 12420; accepted terminal survival inclusion target 4256f782-3b6d-4b44-adf5-367a4cc593d8 candidate 12419; pinned Mathlib lintegral_mono/lintegral_indicator.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_Ioc_discount_record_bounds_of_survival
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_full_reward_indicator_expectation

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierSupValue_ge_survived_interval_discounted_record
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q s t : ℝ)
    (hq : 0 ≤ q) (hs : 0 ≤ s) :
    (∫⁻ ω, if ENNReal.ofReal t < barrierRuinTime X a ω
       then ENNReal.ofReal (Real.exp (-(q * t))) *
         ENNReal.ofReal
           (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω)
       else 0 ∂P) ≤ barrierSupValue X a q := by sorry
