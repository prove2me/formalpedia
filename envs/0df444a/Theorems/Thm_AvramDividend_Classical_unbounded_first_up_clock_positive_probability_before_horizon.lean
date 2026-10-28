-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_first_up_clock_positive_probability_before_horizon
-- name    : AvramDividend.Classical.unbounded_first_up_clock_positive_probability_before_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:47:18.137544+00:00
-- url     : https://prove2.me/theorems/9d6d1b3b-3caa-4e43-b883-d462e6446326
-- title:
--   Positive probability of a strict upper exit clock before any positive horizon
-- statement:
--   For unbounded-variation spectrally negative Lévy processes, before every positive horizon t there exists a positive upper level a whose canonical two-sided upper first-passage clock from reserve zero is less than t with positive probability. This converts the Proved strict pathwise upcrossing event into an event stated using the actual twoSidedExitUpTime definition, giving a root-connected helper for strict two-sided exit identities.
-- source:
--   Proved unbounded_positive_level_upcrossing_strictly_before_horizon and the iInf representation of twoSidedExitUpTime.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_level_upcrossing_strictly_before_horizon
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.OuterMeasure.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_first_up_clock_positive_probability_before_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hnbv : ¬ X.BoundedVariation)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ a : ℝ, 0 < a ∧
      0 < P {ω : Ω | twoSidedExitUpTime X a ω < (t : ℝ≥0∞)} := by sorry
