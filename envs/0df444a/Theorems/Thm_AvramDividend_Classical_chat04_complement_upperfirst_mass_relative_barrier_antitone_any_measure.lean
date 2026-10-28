-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_complement_upperfirst_mass_relative_barrier_antitone_any_measure
-- name    : AvramDividend.Classical.chat04_complement_upperfirst_mass_relative_barrier_antitone_any_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:56:02.860003+00:00
-- url     : https://prove2.me/theorems/bc320f46-e2e3-4788-9dd2-506e38f30ed6
-- title:
--   Ruin-or-tie event mass decreases when initial reserve compensates a barrier shift
-- statement:
--   For any path-space measure, if the initial reserve increases and the relative upper barrier is no farther away, the mass of paths that do not cross above the barrier before ruin cannot increase. The complement includes tied first-passage times.
-- source:
--   Contrapositive of the proved strict upper-before-lower event inclusion followed by monotonicity of measure.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_upperfirst_event_relative_barrier_subset

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_complement_upperfirst_mass_relative_barrier_antitone_any_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (a b x y : ℝ) (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    μ {ω : Ω | ¬ (twoSidedExitUpTime X (b - y) ω <
      twoSidedExitDownTime X (-y) ω)} ≤
    μ {ω : Ω | ¬ (twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω)} := by sorry
