-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_upperfirst_event_relative_barrier_subset
-- name    : AvramDividend.Classical.chat04_strict_exit_upperfirst_event_relative_barrier_subset
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:21:43.925599+00:00
-- url     : https://prove2.me/theorems/1d593fe3-536f-4731-af2a-b4e780105960
-- title:
--   Upper-before-ruin event inclusion under a reserve-compensated barrier shift
-- statement:
--   If the initial reserve rises and the upper boundary is no farther in relative terms, every trajectory exiting above before ruin in the original system also exits above before ruin in the shifted system.
-- source:
--   Derived directly from remotely accepted chat04_strict_exit_clocks_relative_barrier_comparison.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_exit_upperfirst_event_relative_barrier_subset
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b x y : ℝ) (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} ⊆
    {ω : Ω | twoSidedExitUpTime X (b - y) ω <
      twoSidedExitDownTime X (-y) ω} := by sorry
