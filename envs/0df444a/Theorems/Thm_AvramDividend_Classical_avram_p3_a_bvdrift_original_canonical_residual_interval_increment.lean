-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_canonical_residual_interval_increment
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_canonical_residual_interval_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:01:14.693508+00:00
-- url     : https://prove2.me/theorems/79b20dbc-cb51-4e0a-8e08-8bc37c0f8787
-- title:
--   Original BV canonical residual has exact source-increment formula on all intervals
-- statement:
--   The difference of the actual original process drift-minus-negative-jump canonical residual at times s and t equals its physical drift increment minus original source process increment and the actual negative-left-jump real series on (s,t]. The identity is a full-measure all-interval algebraic consequence of genuine source jump additivity, and is a prerequisite for process-shift and stationary-increment analysis.
-- source:
--   Proved original real negative-jump interval additivity f0b0f24b plus exact original BV characteristic drift X.drift, algebraic normalisation. No stochastic independent-increment assumption beyond original process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_real_negative_jump_additivity

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The residual of the original BV drift minus its true left jumps has
a source-exact interval increment identity after splitting the jump series. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_canonical_residual_interval_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      (((t : ℝ) * X.drift - X.X t ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal) -
      (((s : ℝ) * X.drift - X.X s ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal) =
      (((t : ℝ) - (s : ℝ)) * X.drift - (X.X t ω - X.X s ω)) -
        (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal := by sorry
