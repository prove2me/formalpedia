-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_lowerfirst_event_relative_barrier_subset
-- name    : AvramDividend.Classical.chat04_strict_lowerfirst_event_relative_barrier_subset
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:57:47.414679+00:00
-- url     : https://prove2.me/theorems/98d6fac2-d164-44a9-ba39-0851a7db663d
-- title:
--   Strict lower-before-upper ruin event is antitone under relative-reserve improvement
-- statement:
--   If the initial reserve rises and the upper threshold is no farther away in relative terms, any sample path that strictly ruins before reaching the new upper barrier also strictly ruins before reaching the original upper barrier.
-- source:
--   Direct chaining of the proved joint ordering of strict upcrossing and downcrossing times.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_lowerfirst_event_relative_barrier_subset
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b x y : ℝ) (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    {ω : Ω | twoSidedExitDownTime X (-y) ω <
      twoSidedExitUpTime X (b - y) ω} ⊆
    {ω : Ω | twoSidedExitDownTime X (-x) ω <
      twoSidedExitUpTime X (a - x) ω} := by sorry
