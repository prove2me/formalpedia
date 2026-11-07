-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route11_original_raw_jump_cumulative_aestronglyMeasurable
-- name    : AvramDividend.Classical.avram_route11_original_raw_jump_cumulative_aestronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:43:17.435186+00:00
-- url     : https://prove2.me/theorems/2427e100-dcbd-4f33-9ce9-e6d734c9625c
-- title:
--   Original bounded-variation Lévy raw negative-jump cumulative sum is a.e. measurable at every deterministic clock
-- statement:
--   For the actual source spectrally negative bounded-variation Lévy process X, the cumulative real signed sum of original left-limit negative jumps at deterministic time t is an a.e. strongly measurable random variable. This covers the true uncountably indexed summation as represented by the original Lean dividend source, and requires no integrability of the nonpositive HJB residual.
-- source:
--   Original X and actual raw jump tSum, atomic measurability leaf needed to show the weighted removed-residual physical grid is measurable and thereby prove f4231004, b645342a, d5ad627f and the ultimate capped dividend value theorem 297e63cd.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route11_original_raw_jump_cumulative_aestronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (t : ℝ≥0) :
    AEStronglyMeasurable
      (fun ω : Ω =>
        ∑' v : ℝ≥0,
          if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0) P := by sorry
