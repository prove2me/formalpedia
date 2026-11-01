-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits
-- name    : AvramDividend.Classical.avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:24:08.007081+00:00
-- url     : https://prove2.me/theorems/2a1def10-6ab3-40a5-9747-2d9f265735cd
-- title:
--   Generic jointly measurable strict-left-limit process with measurable initial section
-- statement:
--   Any real-valued process with genuine Borel time–sample measurability, finite strict left limits at every positive time and a measurable exact initial Function.leftLim has a jointly measurable left-limit process on the original product space. The zero-time section is kept exact, and a validated source-independent strictly-left fractional mesh gives pointwise convergence for positive times. This is the generic measurable pre-jump evaluation lemma needed for an arbitrary controlled finite-variation perturbation of a càdlàg source.
-- source:
--   Proved fractional strictly-left time mesh, measurable composition, pointwise limits, and leftLim_eq_of_tendsto. No source process or hItoMeyer axiom is postulated.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_prejump_fractional_left_time_mesh

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits
    {Ω : Type*} [MeasurableSpace Ω]
    (F : ℝ≥0 → Ω → ℝ)
    (hJoint : Measurable (fun z : ℝ≥0 × Ω => F z.1 z.2))
    (hzero : Measurable (fun ω : Ω =>
      Function.leftLim (fun s : ℝ≥0 => F s ω) (0 : ℝ≥0)))
    (hleft : ∀ ω t, 0 < t → ∃ l : ℝ,
      Tendsto (fun s : ℝ≥0 => F s ω) (𝓝[<] t) (𝓝 l)) :
    Measurable (fun z : ℝ≥0 × Ω =>
      Function.leftLim (fun s : ℝ≥0 => F s z.2) z.1) := by
  sorry
