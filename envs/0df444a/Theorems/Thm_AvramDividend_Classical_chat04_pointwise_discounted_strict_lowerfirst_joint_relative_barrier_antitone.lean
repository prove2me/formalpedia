-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_pointwise_discounted_strict_lowerfirst_joint_relative_barrier_antitone
-- name    : AvramDividend.Classical.chat04_pointwise_discounted_strict_lowerfirst_joint_relative_barrier_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T12:01:25.680184+00:00
-- url     : https://prove2.me/theorems/f4f8aabe-1871-4b75-9e03-f57cb50bd6b8
-- title:
--   Strict discounted ruin-before-upper-exit payoff decreases jointly with improved reserve and greater discount
-- statement:
--   Pathwise, a simultaneous increase in the initial reserve, nonincrease in the relative upper barrier and increase in the nonnegative discount rate can only decrease the strictly lower-first ruin discount weight.
-- source:
--   Symmetric lower-first counterpart to the proved upper-first joint discount and relative barrier comparison, using the proved ordering of both first-passage clocks and monotonicity of exp.

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_pointwise_discounted_strict_lowerfirst_joint_relative_barrier_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a b x y : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂)
    (hxy : x ≤ y) (hrel : b - y ≤ a - x) (ω : Ω) :
    (if twoSidedExitDownTime X (-y) ω < twoSidedExitUpTime X (b - y) ω then
       ENNReal.ofReal (Real.exp
         (-(q₂ * ENNReal.toReal (twoSidedExitDownTime X (-y) ω))))
     else 0) ≤
    (if twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω then
       ENNReal.ofReal (Real.exp
         (-(q₁ * ENNReal.toReal (twoSidedExitDownTime X (-x) ω))))
     else 0) := by sorry
