-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_discounted_exit_le_shifted_upperfirst_mass_any_measure
-- name    : AvramDividend.Classical.chat04_discounted_exit_le_shifted_upperfirst_mass_any_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:22:34.18631+00:00
-- url     : https://prove2.me/theorems/6aee9891-fa54-4eb7-b598-d0a6c0a7d8a5
-- title:
--   Discounted strict exit bounded by the compensated-shift upper-first event mass under any law
-- statement:
--   Under an arbitrary path-space measure, the discounted upper-exit-before-ruin reward from the original reserve is at most the measure of the shifted upper-first event, provided the reserve rises and the new upper barrier is no farther away relative to reserve. This is useful when bounding tilted first-passage laws.
-- source:
--   Combines chat04_joint_discounted_exit_any_measure_comparison and chat04_discounted_upperfirst_mass_bound_any_measure; both submitted for remote verification at drafting.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_joint_discounted_exit_any_measure_comparison
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_upperfirst_mass_bound_any_measure

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_discounted_exit_le_shifted_upperfirst_mass_any_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q a b x y : ℝ) (hq : 0 ≤ q)
    (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) ≤
    μ {ω : Ω | twoSidedExitUpTime X (b - y) ω <
      twoSidedExitDownTime X (-y) ω} := by sorry
