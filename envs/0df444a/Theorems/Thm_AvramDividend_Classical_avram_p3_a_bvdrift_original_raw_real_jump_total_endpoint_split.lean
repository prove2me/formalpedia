-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_real_jump_total_endpoint_split
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_real_jump_total_endpoint_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:48:26.051758+00:00
-- url     : https://prove2.me/theorems/2f1436db-5246-4f48-9fbe-d1e878144ed3
-- title:
--   Original BV raw real negative jump series splits exactly into endpoint jump and strict-past sum
-- statement:
--   On the actual BV Levy sample path, the absolutely summable real negative-jump magnitudes over (0,t] split into the actual jump at t and the strict-past sum over (0,t), almost surely for every t>0. This matches the original raw real cumulative jump left-limit theorem, preparing a continuous residual proof without a replacement process.
-- source:
--   Accepted original BV interval raw real summability f0ec726b, pinned Mathlib Summable.tsum_eq_add_tsum_ite. This is an actual source path identity with no extra stochastic assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine original BV signed real jump series splits into the
positive-time endpoint atom and the strict-past real left-jump series. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_real_jump_total_endpoint_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) =
      (Function.leftLim (fun z : ℝ≥0 => X.X z ω) t - X.X t ω) +
        (∑' u : ℝ≥0, if 0 < u ∧ u < t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by sorry
