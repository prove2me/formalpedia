-- Prove2me | Theorems.Thm_AvramDividend_Classical_shiftedLevy_increments_right_continuous
-- name    : AvramDividend.Classical.shiftedLevy_increments_right_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:15:36.353497+00:00
-- url     : https://prove2.me/theorems/b901917f-42e9-46f0-ba36-2c3e432afe6d
-- title:
--   Time-shifted Lévy path increments remain right-continuous
-- statement:
--   Fix a spectrally negative Lévy sample path and an arbitrary nonnegative shift u. The shifted increment function r↦X(u+r)−X(u) is right-continuous at every nonnegative r. This supplies the input path continuity for the shifted-running-supremum Stieltjes measure identity.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.ContinuousOn

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.shiftedLevy_increments_right_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0) :
    ∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun r : ℝ≥0 => X.X (u + r) ω - X.X u ω)
        (Set.Ici t) t := by sorry
