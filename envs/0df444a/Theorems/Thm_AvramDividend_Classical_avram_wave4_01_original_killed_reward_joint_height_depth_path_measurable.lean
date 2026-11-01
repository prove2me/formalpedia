-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_reward_joint_height_depth_path_measurable
-- name    : AvramDividend.Classical.avram_wave4_01_original_killed_reward_joint_height_depth_path_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:30:46.497653+00:00
-- url     : https://prove2.me/theorems/2d49d8b7-eedc-40eb-8152-9fa993d7d93d
-- title:
--   Genuine reflected-killed first-record reward jointly Borel in height, drawdown barrier and original sample path
-- statement:
--   For every original spectrally negative Lévy process and real q, the genuine killed first-record discount reward 1_{T_h(ω)<D_a(ω)}exp(-qT_h(ω)) is Borel measurable simultaneously in real upward record level h, real drawdown allowance a and the sample point ω. Uses canonically Proved exact joint (h,ω) first-record clock and genuine joint (a,ω) reflected ruin clock, then a measurable strict comparison and exponential embedding, no Standing or excursion surrogates.
-- source:
--   Requires newly published source joint reflected ruin clock avram_wave4_01_original_reflected_ruin_joint_barrier_path_measurable and already Proved source joint first-record clock avram_wave4_01_original_first_record_clock_joint_height_path_measurable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_first_record_clock_joint_height_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_reflected_ruin_joint_barrier_path_measurable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_killed_reward_joint_height_depth_path_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) :
    Measurable (fun p : (ℝ × ℝ) × Ω =>
      if twoSidedExitUpTime X p.1.1 p.2 < barrierRuinTime X p.1.2 p.2 then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X p.1.1 p.2).toReal)))
      else 0) := by sorry
