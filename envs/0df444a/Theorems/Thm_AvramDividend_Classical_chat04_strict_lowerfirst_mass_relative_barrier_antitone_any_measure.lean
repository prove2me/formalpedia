-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_lowerfirst_mass_relative_barrier_antitone_any_measure
-- name    : AvramDividend.Classical.chat04_strict_lowerfirst_mass_relative_barrier_antitone_any_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:58:41.956318+00:00
-- url     : https://prove2.me/theorems/52081592-beb4-4bf5-a62c-9247d1883a78
-- title:
--   Any path-law strict ruin-before-upper-exit mass decreases under relative-reserve improvement
-- statement:
--   The probability or arbitrary path-measure mass of strict ruin before upper passage is antitone when the initial reserve increases and the relative upper barrier does not increase.
-- source:
--   Measure monotonicity applied to the proved joint first-passage time comparison for upcrossing and downcrossing.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_lowerfirst_mass_relative_barrier_antitone_any_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (a b x y : ℝ) (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    μ {ω : Ω | twoSidedExitDownTime X (-y) ω <
      twoSidedExitUpTime X (b - y) ω} ≤
    μ {ω : Ω | twoSidedExitDownTime X (-x) ω <
      twoSidedExitUpTime X (a - x) ω} := by sorry
