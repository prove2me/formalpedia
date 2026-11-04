-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_canonical_residual_nonnegative_time
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_canonical_residual_nonnegative_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:59:15.526985+00:00
-- url     : https://prove2.me/theorems/3d472a44-c91a-40ef-a519-e37f7311eedf
-- title:
--   Actual original BV canonical drift-minus-jump residual is nonnegative at all times
-- statement:
--   On one full-measure event under the original spectrally negative bounded-variation Lévy process, the original physical drift increment minus the source path and all actual original negative left jumps is nonnegative at every time. This follows from proved monotonicity plus the exact source zero-time value and does not assume the residual vanishes.
-- source:
--   Proved source monotone residual 019edf01, and Proved pathwise original zero-time residual 63f6215d. Same original path and law; no jump-law assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_canonical_residual_zero_at_origin

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original BV drift-minus-jump canonical remainder is nonnegative
at every original sample-path time, starting exactly at zero. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_canonical_residual_nonnegative_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      0 ≤ ((t : ℝ) * X.drift - X.X t ω) -
        (∑' (u : ℝ≥0),
          if 0 < u ∧ u ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal := by sorry
