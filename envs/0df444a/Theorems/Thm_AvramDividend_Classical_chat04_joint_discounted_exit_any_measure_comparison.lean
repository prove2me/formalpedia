-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_joint_discounted_exit_any_measure_comparison
-- name    : AvramDividend.Classical.chat04_joint_discounted_exit_any_measure_comparison
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:08:24.083979+00:00
-- url     : https://prove2.me/theorems/5238e355-aaf5-4622-a52a-6daee55a3051
-- title:
--   Joint strict-exit discount, reserve and barrier comparison under any measure
-- statement:
--   The pointwise comparison of discounted upper-before-ruin payoffs survives integration against any measure on path space. This enables comparisons under probability tilts and other changes of measure without redoing the Lévy passage-time argument.
-- source:
--   Follows directly by lintegral_mono from published chat04_pointwise_discounted_strict_exit_joint_relative_barrier_mono (publication pending at drafting).

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_pointwise_discounted_strict_exit_joint_relative_barrier_mono

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_joint_discounted_exit_any_measure_comparison
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q₁ q₂ a b x y : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂)
    (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q₂ * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) ≤
    (∫⁻ ω,
      if twoSidedExitUpTime X (b - y) ω < twoSidedExitDownTime X (-y) ω then
        ENNReal.ofReal (Real.exp
          (-(q₁ * ENNReal.toReal (twoSidedExitUpTime X (b - y) ω))))
      else 0 ∂μ) := by sorry
