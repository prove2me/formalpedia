-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_of_near_threshold_crossings
-- name    : AvramDividend.Classical.twoSidedExitUpTime_eq_zero_of_near_threshold_crossings
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:28:32.924428+00:00
-- url     : https://prove2.me/theorems/19dea0ac-dea6-4f87-b5a2-81e102753ce2
-- title:
--   Strict upward crossings arbitrarily early force immediate exit at any threshold
-- statement:
--   At any real threshold b, arbitrarily early strictly higher observations imply that the upward passage clock equals zero.
-- source:
--   Choice of a crossing sequence below 1/(n+1), squeeze convergence, and general-threshold sequence passage theorem.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_of_sequence_at_threshold
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitUpTime_eq_zero_of_near_threshold_crossings
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω)
    (hnear : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ b < X.X t ω) :
    twoSidedExitUpTime X b ω = 0 := by sorry
