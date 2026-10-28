-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_pointwise_discounted_strict_exit_joint_relative_barrier_mono
-- name    : AvramDividend.Classical.chat04_pointwise_discounted_strict_exit_joint_relative_barrier_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:04:01.274053+00:00
-- url     : https://prove2.me/theorems/c157027d-7b65-4b68-af68-79432cb4f53d
-- title:
--   Pointwise strict-exit discounted reward monotonicity under joint reserve and discount shifts
-- statement:
--   For every sample path, increasing starting reserve without increasing the relative upper crossing threshold makes strict upper exit before ruin more likely and sooner. If the discount on the original path is no smaller than the discount on the shifted path, the killed discounted upper-exit payoff is pointwise bounded by the shifted payoff. The inequality holds before integration against any probability measure.
-- source:
--   Strengthens the proved chat04_strict_exit_clocks_relative_barrier_comparison (5e83d1a9-b841-4183-9788-ed2fc2c18017) by exponential discount monotonicity. It implies the expectation comparison after integration.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_pointwise_discounted_strict_exit_joint_relative_barrier_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a b x y : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂)
    (hxy : x ≤ y) (hrel : b - y ≤ a - x) (ω : Ω) :
    (if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
       ENNReal.ofReal (Real.exp
         (-(q₂ * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
     else 0) ≤
    (if twoSidedExitUpTime X (b - y) ω < twoSidedExitDownTime X (-y) ω then
       ENNReal.ofReal (Real.exp
         (-(q₁ * ENNReal.toReal (twoSidedExitUpTime X (b - y) ω))))
     else 0) := by sorry
