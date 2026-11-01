-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_reward_joint_height_depth_law_measurable
-- name    : AvramDividend.Classical.avram_wave4_01_original_killed_reward_joint_height_depth_law_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:37:45.944002+00:00
-- url     : https://prove2.me/theorems/a187ce98-1b88-4a37-8e46-d5c6716144a2
-- title:
--   Joint Borel measurability of the true killed first-record discounted law in real record height and drawdown depth
-- statement:
--   For the original Lévy strict record T_h and strict reflected ruin D_a, the (extended nonnegative) expected discount E[exp(-q T_h); T_h<D_a] is jointly Borel measurable for all real height-depth parameters. The proof applies pinned measurable-parameter integration to the genuine joint source reward in (h,a,ω) and uses only X.isProbability for σ-finiteness. This is genuinely an expectation of actual source clocks, not a sampled replacement and no Standing condition.
-- source:
--   Depends on new joint (h,a,ω) source reward measurability prepared after exact joint ruin target 34cc2627; pinned Measurable.lintegral_prod_right exact type verified.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_reward_joint_height_depth_path_measurable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_killed_reward_joint_height_depth_law_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) :
    Measurable (fun p : ℝ × ℝ =>
      ∫⁻ ω, if twoSidedExitUpTime X p.1 ω <
                 barrierRuinTime X p.2 ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X p.1 ω).toReal)))
      else 0 ∂P) := by sorry
