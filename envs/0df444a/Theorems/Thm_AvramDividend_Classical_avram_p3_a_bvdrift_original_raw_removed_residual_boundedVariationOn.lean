-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_boundedVariationOn
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_boundedVariationOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:21:49.355401+00:00
-- url     : https://prove2.me/theorems/27f4ee33-3d20-44a5-89ff-49e6f2d17a8a
-- title:
--   Original BV source real negative jump residual has finite total variation on every time interval
-- statement:
--   For one full event of the same original bounded-variation Levy source, the physical drift residual after removing actual raw real negative left jumps is of bounded variation on each compact interval. This is directly suitable for deterministic Lebesgue-Stieltjes/C1 change-of-variables work, without assuming that residual vanishes.
-- source:
--   P3-A actual original raw drift residual monotonicity and pinned Mathlib monotone compact variation theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_monotone_real_path_compact_boundedVariation

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The true original BV source residual after removing actual negative
jumps has bounded total variation on every finite time interval. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_boundedVariationOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ≥0, a ≤ b →
      BoundedVariationOn (fun t : ℝ≥0 =>
        (((t : ℝ) * X.drift - X.X t ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)))
        (Icc a b) := by sorry
