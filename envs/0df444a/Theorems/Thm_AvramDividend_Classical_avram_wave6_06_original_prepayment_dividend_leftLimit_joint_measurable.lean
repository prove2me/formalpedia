-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_prepayment_dividend_leftLimit_joint_measurable
-- name    : AvramDividend.Classical.avram_wave6_06_original_prepayment_dividend_leftLimit_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:18:00.263961+00:00
-- url     : https://prove2.me/theorems/1816332a-699b-4fd5-9aa3-706aef760f9d
-- title:
--   Original strict-left dividend path D+ has exact jointly measurable prepayment limit
-- statement:
--   For actual original adapted left-continuous dividends D, show jointly measurable strict-left limit of the right-continuous D+ including exact initial Function.leftLim at zero. Use Proved rightLimit fixed-time measurable, right-continuity, finite left limits and generic joint left-limit theorem. This is an exact source input to the actual ruin-endpoint book reserve, no stochastic Ito identity or substitute control.
-- source:
--   Avram Proposition 4(i) source book-value at positive ruin and D_{t+} Stieltjes convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_has_leftLimits
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_prepayment_dividend_leftLimit_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun z : ℝ≥0 × Ω =>
      Function.leftLim (fun s : ℝ≥0 => rightLimit D s z.2) z.1) := by sorry
