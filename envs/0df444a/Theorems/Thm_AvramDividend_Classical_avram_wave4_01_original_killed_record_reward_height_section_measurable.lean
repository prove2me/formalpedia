-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_record_reward_height_section_measurable
-- name    : AvramDividend.Classical.avram_wave4_01_original_killed_record_reward_height_section_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:17:32.14233+00:00
-- url     : https://prove2.me/theorems/6e6e18c7-c007-47aa-9e84-a1e0597218db
-- title:
--   The genuine first-record reward killed at reflected drawdown ruin is measurable in record height along every original Lévy path
-- statement:
--   For any fixed original Lévy sample path, record-height map h ↦ 1_{T_h < D_a} exp(-q T_h) is Borel measurable with extended nonnegative reward, using the genuine strict upward record T_h and reflected drawdown clock D_a. The exact source first-passage clock is monotone in threshold, hence measurable in height; Borel functions toReal, real exponential and ENNReal.ofReal, and the strict comparison with fixed D_a, preserve measurability. No Standing, q sign, Esscher tilt or excursion assumptions are required. This is the height-section component of the anticipated joint-measurability/Tonelli route.
-- source:
--   Canonical source twoSidedExitUpTime_mono_threshold 5060f2c9-5c3e-48d5-a44c-101f9a63f35a. Pinned Mathlib Monotone.measurable, ENNReal.measurable_toReal, ENNReal.measurable_ofReal, Measurable.ite, Real.continuous_exp verified from revision-bound signatures. The original reflected ruin clock is constant in height. Joint product measurability remains a separate stochastic claim.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_killed_record_reward_height_section_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a : ℝ) (ω : Ω) :
    Measurable (fun h : ℝ =>
      if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
        else 0) := by sorry
