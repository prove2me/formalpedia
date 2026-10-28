-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_of_positive_near_zero
-- name    : AvramDividend.Classical.twoSidedExitUpTime_eq_zero_of_positive_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:48:37.887411+00:00
-- url     : https://prove2.me/theorems/976ee68d-a77b-4c5a-9a9b-ac57eb66c687
-- title:
--   Positive observations arbitrarily close to zero force immediate two-sided upper exit
-- statement:
--   If a Lévy path has positive observations at arbitrarily small positive time radii, its canonical two-sided upper exit clock at zero equals zero. Construct a convergent sequence of witness times.
-- source:
--   Pathwise first passage consequence for spectrally negative Lévy processes.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_of_positive_sequence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitUpTime_eq_zero_of_positive_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hnear : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    twoSidedExitUpTime X 0 ω = 0 := by sorry
