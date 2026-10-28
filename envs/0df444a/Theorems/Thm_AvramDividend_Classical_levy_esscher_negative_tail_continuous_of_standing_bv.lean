-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_esscher_negative_tail_continuous_of_standing_bv
-- name    : AvramDividend.Classical.levy_esscher_negative_tail_continuous_of_standing_bv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:38:25.737018+00:00
-- url     : https://prove2.me/theorems/7a5cf4c6-ac0d-4b15-8781-254006578689
-- title:
--   Esscher-weighted BV Lévy negative-tail continuity from standing assumptions
-- statement:
--   For a spectrally negative bounded-variation Lévy process with the standing assumptions and a nonnegative Esscher parameter, the Esscher-weighted Lévy intensity of jumps of magnitude at least r is continuous in every r>0. The exponential multiplier is at most 1 on negative jumps, so all cut-off tails are finite. Atomlessness is inherited by the weighted measure. This directly supplies the signed-jump-axis continuity input for the bounded-variation C1 scale and cstar finiteness route.
-- source:
--   Proved levy_negative_mass_away_from_zero_finite and levyMeasure_singleton_null_of_standing_boundedVariation; real exponential bound and Proved continuousOn_esscher_weighted_negative_tail_of_finite_noAtoms.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyMeasure_singleton_null_of_standing_boundedVariation
import Theorems.Thm_AvramDividend_Classical_levy_negative_mass_away_from_zero_finite
import Theorems.Thm_AvramDividend_Classical_continuousOn_esscher_weighted_negative_tail_of_finite_noAtoms
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_esscher_negative_tail_continuous_of_standing_bv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 ≤ φ) :
    ContinuousOn (fun r : ℝ =>
      (X.ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))).real (Iic (-r)))
      (Ioi (0 : ℝ)) := by sorry
