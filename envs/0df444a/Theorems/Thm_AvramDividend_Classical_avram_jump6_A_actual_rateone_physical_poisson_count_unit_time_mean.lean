-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_rateone_physical_poisson_count_unit_time_mean
-- name    : AvramDividend.Classical.avram_jump6_A_actual_rateone_physical_poisson_count_unit_time_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:31:50.176855+00:00
-- url     : https://prove2.me/theorems/cc7561fc-931b-4b9a-9076-b22ca5438a8a
-- title:
--   Physical rate-one Poisson count has unit expected value at time one
-- statement:
--   The original rate-one Poisson jump count at unit time has expectation exactly one on its actual physical probability space, given its measurable true Poisson(1) marginal law. This supplies the missing original one-step drift identification E[B1−2N1]=−2 for the Brownian-plus-size-two-negative-Poisson model, and hence the actual compensating +2t term in the Jfull source rather than an assumed mean. Apply the previously Proved Mathlib-pin rate-one Poisson integral source 951829c1 and change-of-variables for the genuine map law.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_count_expected_rate_ws01b
set_option autoImplicit false
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_actual_rateone_physical_poisson_count_unit_time_mean
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (N : Ω → ℕ)
    (hNm : Measurable N)
    (hLaw : P.map N = poissonMeasure (1 : ℝ≥0)) :
    (∫ ω, (N ω : ℝ) ∂P) = 1 := by sorry
