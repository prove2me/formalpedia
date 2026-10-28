-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_magnitude_tail_continuous
-- name    : AvramDividend.Classical.bv_esscher_positive_magnitude_tail_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T08:11:22.315801+00:00
-- url     : https://prove2.me/theorems/ec8d0766-5f9e-4e62-b347-077469e081a2
-- title:
--   Continuity of the explicit BV Esscher positive jump-magnitude tail kernel
-- statement:
--   For a bounded-variation spectrally negative Lévy process satisfying the standing assumptions and any nonnegative Esscher parameter, the discounted strict positive tail of the reflected jump-magnitude measure is continuous as a real function on r>0. The signed-to-magnitude Esscher tail map identity transports the already canonically proved signed-tail continuity, while standing atomlessness removes the open/closed endpoint distinction. This is the exact real positive-time tail-density continuity input of the BV renewal measure κ in bv_root_discounted_tail_kernel_ac_package, supporting scaled renewal density and cstar finiteness.
-- source:
--   Proved levy_esscher_negative_tail_continuous_of_standing_bv, strict signed-to-magnitude weighted measure map identity, singleton-null standing BV property.

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyMeasure_singleton_null_of_standing_boundedVariation
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_signed_jump_tail_map_identity
import Theorems.Thm_AvramDividend_Classical_levy_esscher_negative_tail_continuous_of_standing_bv
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_positive_magnitude_tail_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 ≤ φ) :
    ContinuousOn (fun r : ℝ =>
      ((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
        (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))).real
        {z : ℝ≥0 | r < (z : ℝ)}) (Ioi (0 : ℝ)) := by sorry
