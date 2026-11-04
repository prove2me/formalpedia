-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_endpoint_left_jump_tsum_split
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_endpoint_left_jump_tsum_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:02:20.758197+00:00
-- url     : https://prove2.me/theorems/4b729256-b2a4-4699-9cba-1c2fc77ff9f2
-- title:
--   Exact actual original negative left jump endpoint atom decomposes complete jump sum
-- statement:
--   At every positive time and every sample path of the original spectrally negative Levy process, the complete ENNReal sum of actual negative left-jump magnitudes up to that time is exactly the jump magnitude at the endpoint plus the complete sum over strictly earlier positive times. Holds without bounded variation, compensator or auxiliary process representation.
-- source:
--   Specialise pinned Mathlib ENNReal.tsum_eq_add_tsum_ite at the actual source endpoint t. Pointwise set algebra identifies deletion of index t with strict-left time support, using 0<t. This is a necessary endpoint atom identity for a continuous residual proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The complete actual negative left-jump magnitude sum up to a positive
time splits into the genuine jump at that time and all earlier jumps. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_endpoint_left_jump_tsum_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    (∑' (u : ℝ≥0),
      if 0 < u ∧ u ≤ t then
        ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
      else 0) =
      ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) t - X.X t ω) +
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u < t then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0) := by sorry
