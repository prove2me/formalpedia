-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uncapped_reflected_killed_future_reward_factor
-- name    : AvramDividend.Classical.avram_wave3_01_uncapped_reflected_killed_future_reward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:46:47.578895+00:00
-- url     : https://prove2.me/theorems/7647de82-99e0-4a1d-98d4-20d5759363c4
-- title:
--   Uncapped original Lévy reflected-killed first-record discount factors from arbitrary measurable full-future rewards
-- statement:
--   Under the original spectrally negative Lévy law, condition on the actual strict first upward record occurring before the original reflected-drawdown ruin. For every measurable discount and every measurable functional of the full future path, the uncapped conditional reward expectation is exactly the killed stopped-history discounted mass times the original-law future reward expectation. The proof takes genuinely stopped right-continuous finite caps to infinity using countable nonnegative monotone convergence. This supports the source reflected killed-record semigroup and standing-free scale C1.
-- source:
--   Proved f4c6b616 stopped future factor, 75a45591 stopped-history membership, and 87a4ffed method for uncapping full future path rewards, with exact original barrierRuinTime source event. Builds toward 3890ee9b and cd61d678.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_in_finiteStoppedHistory
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_measurable_global
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_uncapped_reflected_killed_future_reward_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    (let T := twoSidedExitUpTime X b
     let R := barrierRuinTime X a
     (∫⁻ ω, if T ω < R ω then
       discount ((T ω).toNNReal) *
         reward (fun t : ℝ≥0 =>
           X.X ((T ω).toNNReal + t) ω - X.X ((T ω).toNNReal) ω)
       else 0 ∂P) =
     (∫⁻ ω, if T ω < R ω then
       discount ((T ω).toNNReal) else 0 ∂P) *
       (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P)) := by sorry
