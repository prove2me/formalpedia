-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_stopping_clock_measurable_from_filtration
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_stopping_clock_measurable_from_filtration
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:46:18.761681+00:00
-- url     : https://prove2.me/theorems/5b2726dd-c822-4229-8ea2-9acdd01630a0
-- title:
--   Original right-continuous stopping time already makes the finite physical clock measurable
-- statement:
--   For a genuinely finite original controlled-process stopping clock τ valued in NNReal, the hypothesis that τ as a WithTop-valued random time is a stopping time of the actual right-continuous filtration already supplies the physical clock measurability needed by the source compensation integrals.
-- source:
--   Mathlib Probability.Process.Stopping IsStoppingTime.measurable and Borel WithTop measurable untopD

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_stopping_clock_measurable_from_filtration {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) : Measurable τ := by sorry
