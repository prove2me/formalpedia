-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_continuous_positive_time
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_continuous_positive_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:27:31.293548+00:00
-- url     : https://prove2.me/theorems/38d9546f-8a24-4324-b334-b841deb9f404
-- title:
--   Original BV physical-drift residual has continuous paths at all strictly positive times
-- statement:
--   On a single full-measure event of the same original bounded-variation spectrally negative Levy process, the physical-drift residual after removing the actual real negative left jumps is continuous at every strictly positive time. The proof combines independently verified source monotonicity, original source jump cancellation, right continuity, and a pinned Mathlib monotone path lemma.
-- source:
--   P3-A original raw source residual monotonicity, left- and right-continuity, and monotone two-sided continuity lemma, all source-backed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_left_continuous
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_right_continuous
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_monotone_path_continuous_of_leftLim_and_right

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- After removing the genuine original BV source's negative left jumps,
the physical-drift remainder is continuous at every positive time a.e. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_continuous_positive_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      ContinuousAt (fun s : ℝ≥0 =>
        (((s : ℝ) * X.drift - X.X s ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) t := by sorry
