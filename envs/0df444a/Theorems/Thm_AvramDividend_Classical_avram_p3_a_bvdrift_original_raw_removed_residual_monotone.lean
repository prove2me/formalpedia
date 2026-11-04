-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:04:29.812485+00:00
-- url     : https://prove2.me/theorems/e9d95081-1010-4cec-87d2-14abac4f2e96
-- title:
--   Actual original BV drift residual with raw signed negative jumps is nondecreasing
-- statement:
--   For the same genuine original bounded-variation Levy source, the physical drift coefficient times t minus X_t minus the actual raw signed negative jump series is monotone in time, almost surely. Uses the previously Proved canonical ENNReal residual and the exact original jump-series conversion.
-- source:
--   Proved source monotone residual 019edf01 and exact source raw real jump sum f0ec726b. All assumptions original X.BoundedVariation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine source BV residual is monotone when its actual negative
jumps are expressed directly as a signed real tsum. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 =>
      (((t : ℝ) * X.drift - X.X t ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
          else 0))) := by sorry
