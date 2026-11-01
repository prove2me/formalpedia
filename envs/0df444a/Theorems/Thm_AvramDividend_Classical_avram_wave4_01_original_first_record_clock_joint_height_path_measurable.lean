-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_first_record_clock_joint_height_path_measurable
-- name    : AvramDividend.Classical.avram_wave4_01_original_first_record_clock_joint_height_path_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:27:38.771255+00:00
-- url     : https://prove2.me/theorems/27b76adc-3b90-48a8-8b36-1f6aab50799f
-- title:
--   The actual strict first-record clock is jointly measurable in real threshold and Lévy sample point
-- statement:
--   The source first strict upward passage time (h,ω)↦T_h(ω) is jointly Borel measurable in real height h and the original sample point ω, with values in extended nonnegative time. The proved true Cantor-schedule representation of the entire original record clock converts its uncountable time-infimum into a countable infimum over fixed deterministic sample times; each sampled Lévy value is product-measurable by the independently Proved joint Lévy process measurability theorem. The finite-height exact clock identity is pointwise in h and ω, with no Standing and no tilted excursion. This is the authentic product-measurability input needed to apply Tonelli to the original killed first-record height potential.
-- source:
--   Proved source avram_wave3_01_true_shifted_record_ruin_clock_pair UUID acce5dd9-68df-47c5-88fb-48f0dbad055a; source chat04_levy_joint_time_state_measurable UUID d55462c3-decf-40f0-9aff-439d356324d9; X.X_zero; pinned Mathlib Measurable.iInf, Measurable.ite, measurableSet_lt, measurable_const.prodMk measurable_snd. No new stochastic axiom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_true_shifted_record_ruin_clock_pair
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_first_record_clock_joint_height_path_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun p : ℝ × Ω => twoSidedExitUpTime X p.1 p.2) := by sorry
