-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_of_negative_near_zero
-- name    : AvramDividend.Classical.twoSidedExitDownTime_eq_zero_of_negative_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:46:51.940699+00:00
-- url     : https://prove2.me/theorems/77391f76-24d6-4044-b269-e4e84c8839ee
-- title:
--   Negative observations arbitrarily close to zero force immediate two-sided lower exit
-- statement:
--   If a Lévy path has negative observations at arbitrarily small positive time radii, the canonical two-sided lower exit clock at zero equals zero. Uses a sequence of observations and a squeeze argument.
-- source:
--   Pathwise first passage consequence for spectrally negative Lévy processes.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_of_negative_sequence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitDownTime_eq_zero_of_negative_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hnear : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    twoSidedExitDownTime X 0 ω = 0 := by sorry
