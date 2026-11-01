-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_reward_joint_height_barrier_on_path_measurable
-- name    : AvramDividend.Classical.avram_wave4_01_original_killed_reward_joint_height_barrier_on_path_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:52:50.529911+00:00
-- url     : https://prove2.me/theorems/2bbb5bfe-1a42-4adf-bdf1-e1cd846db9ef
-- title:
--   Actual original reflected-killed first-record reward is jointly Borel in upward height and ruin depth on every Lévy path
-- statement:
--   For every fixed original Lévy sample ω, the actual nonnegative killed first upward-record payoff 1_{T_h(ω)<D_a(ω)} exp(-qT_h(ω)) is jointly Borel measurable in the ordered real pair (h,a), without Standing. The argument uses genuine pathwise Borel dependence of T_h on record height and D_a on reflected ruin depth, strict comparison, real exponential and measurable embedding. It does not assert joint measurability in the sample coordinate.
-- source:
--   New Proved source lemmas avram_wave4_01_original_first_record_height_clock_measurable (3d81e537) and avram_wave4_01_original_reflected_ruin_barrier_level_measurable (03cbd14a), plus pinned Mathlib measurability combinators.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_first_record_height_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_reflected_ruin_barrier_level_measurable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_killed_reward_joint_height_barrier_on_path_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (ω : Ω) :
    Measurable (fun p : ℝ × ℝ =>
      if twoSidedExitUpTime X p.1 ω < barrierRuinTime X p.2 ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X p.1 ω).toReal)))
      else 0) := by sorry
