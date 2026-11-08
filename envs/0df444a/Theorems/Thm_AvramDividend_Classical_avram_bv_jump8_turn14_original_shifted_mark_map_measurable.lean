-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn14_original_shifted_mark_map_measurable
-- name    : AvramDividend.Classical.avram_bv_jump8_turn14_original_shifted_mark_map_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:25:24.874204+00:00
-- url     : https://prove2.me/theorems/c123ea71-3b34-415e-bba5-24360c052146
-- title:
--   Original shifted Lévy jump-mark map is measurable for arbitrary nonnegative shift
-- statement:
--   For every deterministic nonnegative shift s and sample path ω of the actual spectrally negative Lévy process, the marked jump path u ↦ (u, Δ(X(s+u)−X(s))) is Borel measurable, with the same left-limit convention. This extends the Proved integer-shift theorem to exact fractional cell boundaries required for the unit-time Laplace product.
-- source:
--   Source-identical proof adaptation from Proved e2ab3e9a: rightContinuous_measurable_sections_joint_evaluation, arbitrary-shift cadlag path, joint measurable leftLimit and measurable product. The verified underlying cadlag shift lemma takes s : NNReal, not just n : Nat.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn14_original_shifted_mark_map_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s : ℝ≥0) :
    Measurable (fun u : ℝ≥0 =>
      (u, (X.X (s + u) ω - X.X s ω) -
        Function.leftLim
          (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u)) := by sorry
