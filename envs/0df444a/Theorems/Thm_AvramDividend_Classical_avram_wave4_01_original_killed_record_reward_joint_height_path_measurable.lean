-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_record_reward_joint_height_path_measurable
-- name    : AvramDividend.Classical.avram_wave4_01_original_killed_record_reward_joint_height_path_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:46:55.448994+00:00
-- url     : https://prove2.me/theorems/9427609e-7f2b-4b8d-9ce7-c1e50177e4b3
-- title:
--   The actual reflected-ruin-killed first-record reward is jointly measurable in height and original Lévy sample path
-- statement:
--   The map (h,ω)↦1_{T_h(ω)<D_a(ω)} exp(-q T_h(ω)), in extended nonnegative values with genuine original strict record T and reflected ruin D, is jointly measurable for all real q,a, with no Standing. This combines the authentic jointly measurable first-record clock, source measurable ruin clock, Borel toReal, real exponential and positive embedding, and measurable strict comparison. It is the central product-space requirement for source-law Tonelli and the actual pathwise killed record-height occupation potential.
-- source:
--   Requires newly published joint original record-height clock theorem avram_wave4_01_original_first_record_clock_joint_height_path_measurable; already Proved barrierRuinTime_measurable and pinned Mathlib ENNReal.measurable_toReal, Real.measurable_exp, ENNReal.measurable_ofReal, Measurable.ite. The new joint-clock theorem must be canonically Proved before this target's import and proof submission.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_first_record_clock_joint_height_path_measurable
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_killed_record_reward_joint_height_path_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a : ℝ) :
    Measurable (fun p : ℝ × Ω =>
      if twoSidedExitUpTime X p.1 p.2 < barrierRuinTime X a p.2 then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X p.1 p.2).toReal)))
      else 0) := by sorry
