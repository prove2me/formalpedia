-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_ruin_piecewise_book_postpayment_terminal_measurable
-- name    : AvramDividend.Classical.avram_wave6_06_original_ruin_piecewise_book_postpayment_terminal_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:16:28.138197+00:00
-- url     : https://prove2.me/theorems/06433bf3-0bd7-4114-a5fe-7c072b104606
-- title:
--   Exact original ruin-stopped piecewise book/post-payment terminal is measurable
-- statement:
--   Show measurability on the original sample space of the exact source terminal reserve: post-right-dividend at time zero or strictly pre-ruin, but original pre-right-dividend book reserve at a positive ruin endpoint. Use Proved original joint Borel Levy X and Dplus, Proved left-limit identity D_t=lim_{s↑t}D_s+ for t>0, generic jointly measurable strict-left-limits, original ruin-time measurability and the genuine stopping time. The time-zero branch avoids substituting D_0+ for D_0. No stochastic Ito identity, surrogate process, or BV/UBV branch is assumed.
-- source:
--   Avram Proposition 4(i), finite-horizon terminal convention in Eq (5.11)-(5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopped_postPayment_reserve_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_has_leftLimits
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_ruin_piecewise_book_postpayment_terminal_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    Measurable W := by sorry
