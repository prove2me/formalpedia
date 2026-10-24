-- Prove2me | Theorems.Thm_AvramDividend_Classical_shiftedSup_right_continuous_of_levy
-- name    : AvramDividend.Classical.shiftedSup_right_continuous_of_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:31:16.633064+00:00
-- url     : https://prove2.me/theorems/8b268815-9033-4ad9-9d6d-886df0f701fb
-- title:
--   Running supremum of shifted Lévy increments is right-continuous
-- statement:
--   Fix any Lévy sample path and a nonnegative shift u. The running supremum of increments X(u+r)−X(u) over r∈[0,t] has a right-continuous path in t. This combines interval boundedness, path right-continuity and a generic running-supremum continuity lemma, supplying the right-limit hypothesis for Stieltjes dividend rewards.

import Theorems.Thm_AvramDividend_Classical_intervalSup_right_continuous_of_right_continuous
import Theorems.Thm_AvramDividend_Classical_shiftedLevy_increments_right_continuous
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.shiftedSup_right_continuous_of_levy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0) :
    ∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun r : ℝ≥0 =>
          sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
        (Set.Ici t) t := by sorry
