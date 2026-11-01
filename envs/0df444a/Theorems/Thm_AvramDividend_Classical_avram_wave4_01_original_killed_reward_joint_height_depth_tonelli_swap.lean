-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_reward_joint_height_depth_tonelli_swap
-- name    : AvramDividend.Classical.avram_wave4_01_original_killed_reward_joint_height_depth_tonelli_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:38:03.278521+00:00
-- url     : https://prove2.me/theorems/3fe05916-5f72-40bd-a405-b21da8edffb7
-- title:
--   Two-dimensional Tonelli interchange over genuine strict first-record heights and drawdown depths for original Lévy killed discount
-- statement:
--   For actual strict first record T_h and reflected drawdown strict ruin D_a, the expected integrated killed record reward over all positive record heights h and positive ruin depths a equals the integral over these two parameters of the expected reward. This is a fully three-variable Tonelli equality over the source Lévy law, positive height and depth, with no Standing and no sample-clock substitution. All integrals are ENNReal, so the interchange holds without a finiteness assumption.
-- source:
--   Prepared true joint (h,a,ω) reward measurability 2d49d8b7 and pinned Mathlib lintegral_lintegral_swap, source probability X.isProbability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_reward_joint_height_depth_path_measurable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_killed_reward_joint_height_depth_tonelli_swap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) :
    (∫⁻ ω, ∫⁻ p in (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)),
      (if twoSidedExitUpTime X p.1 ω < barrierRuinTime X p.2 ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X p.1 ω).toReal)))
      else 0) ∂volume ∂P) =
    (∫⁻ p in (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)), ∫⁻ ω,
      (if twoSidedExitUpTime X p.1 ω < barrierRuinTime X p.2 ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X p.1 ω).toReal)))
      else 0) ∂P ∂volume) := by sorry
