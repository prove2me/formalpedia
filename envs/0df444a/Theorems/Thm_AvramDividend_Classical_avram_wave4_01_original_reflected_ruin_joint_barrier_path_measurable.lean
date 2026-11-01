-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_reflected_ruin_joint_barrier_path_measurable
-- name    : AvramDividend.Classical.avram_wave4_01_original_reflected_ruin_joint_barrier_path_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:07:31.275984+00:00
-- url     : https://prove2.me/theorems/34cc2627-96ba-435c-85d5-47ff5bba13b8
-- title:
--   The genuine strict reflected drawdown ruin time is jointly Borel measurable in barrier level and original Lévy sample path
-- statement:
--   The actual extended nonnegative reflected drawdown ruin clock D_a(ω) is jointly Borel measurable in real barrier a and original sample ω, without Standing. The true strict-breach pathwise clock equals an infimum over countable Cantor-rational observation times. At each sampled time, the original Lévy value and genuine running supremum are jointly measurable in time and ω, and the strict drawdown breach test with variable a is a Borel comparison. Therefore each sampled indicator clock is product-measurable and their countable infimum equals D_a pointwise. No separate-measurability shortcut or stochastic axiom.
-- source:
--   Proved genuine sampled strict clock reflectedRuin_strictClock_eq_countableSchedule 253a6335; Proved source bridge avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock 75280f18; Proved joint X  d55462c3 and joint runningSup ecfe330c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock
import Theorems.Thm_AvramDividend_Classical_reflectedRuin_strictClock_eq_countableSchedule
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_reflected_ruin_joint_barrier_path_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun p : ℝ × Ω => barrierRuinTime X p.1 p.2) := by sorry
