-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_magnitude_cumulative_boundedVariationOn
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_jump_magnitude_cumulative_boundedVariationOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:21:51.454311+00:00
-- url     : https://prove2.me/theorems/23d8065e-2993-4704-8264-02e8eea7c9fa
-- title:
--   Original BV source actual negative jump magnitude sum has bounded variation on each compact interval
-- statement:
--   On one full-measure original source event, the cumulative sum of actual negative left-jump magnitudes is a finite-total-variation real path on every compact interval, using original BV jumps and monotonicity. This yields an integration-ready Stieltjes source term.
-- source:
--   P3-A original actual ENNReal jump magnitude cumulative monotonicity 0759bddb and pinned compact monotone bounded variation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_real_jump_total_monotone_time
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_monotone_real_path_compact_boundedVariation

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original BV source cumulative negative jump magnitude process
has bounded total variation on each finite interval. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_jump_magnitude_cumulative_boundedVariationOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ≥0, a ≤ b →
      BoundedVariationOn (fun t : ℝ≥0 =>
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal)
        (Icc a b) := by sorry
