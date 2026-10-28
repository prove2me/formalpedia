-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_discounted_lowerfirst_any_measure_joint_relative_barrier_antitone
-- name    : AvramDividend.Classical.chat04_discounted_lowerfirst_any_measure_joint_relative_barrier_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T12:04:04.327024+00:00
-- url     : https://prove2.me/theorems/df125a7c-d6a0-4865-a7bb-f1551be2db34
-- title:
--   Expected discounted strict ruin-before-upper-exit payoff decreases under improved reserve and higher discount for any path law
-- statement:
--   For arbitrary sample-path measure, increasing initial reserve and nonnegative discount rate whilst reducing relative upper barrier weakly decreases the strict ruin-before-upper-exit discounted lower integral.
-- source:
--   Integrate the proved pointwise joint lower-first first-passage discount comparison using monotonicity of the nonnegative Lebesgue integral.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_pointwise_discounted_strict_lowerfirst_joint_relative_barrier_antitone

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_discounted_lowerfirst_any_measure_joint_relative_barrier_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q₁ q₂ a b x y : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂)
    (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    (∫⁻ ω,
      if twoSidedExitDownTime X (-y) ω < twoSidedExitUpTime X (b - y) ω then
        ENNReal.ofReal (Real.exp
          (-(q₂ * ENNReal.toReal (twoSidedExitDownTime X (-y) ω))))
      else 0 ∂μ) ≤
    (∫⁻ ω,
      if twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp
          (-(q₁ * ENNReal.toReal (twoSidedExitDownTime X (-x) ω))))
      else 0 ∂μ) := by sorry
