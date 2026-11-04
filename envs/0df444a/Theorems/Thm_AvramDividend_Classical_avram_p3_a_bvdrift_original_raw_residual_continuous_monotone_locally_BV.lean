-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_residual_continuous_monotone_locally_BV
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_residual_continuous_monotone_locally_BV
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:58:20.595723+00:00
-- url     : https://prove2.me/theorems/1de836ec-abc6-451d-a6b4-8a2070bc2b51
-- title:
--   Original BV Levy raw jump-removed residual is continuous increasing and locally of bounded variation on one full event
-- statement:
--   There is one original-probability full event on which the actual raw-jump-removed physical drift residual is continuous at every nonnegative time including zero, monotone, and of bounded variation on every compact nonnegative interval. All properties come from accepted original-source theorems, with no representation, rate, compensator, or drift identity assumed.
-- source:
--   Accepted source theorems 56ed0b8e-04ab-40f9-ac91-f7e5cabdf46b, e9d95081-1010-4cec-87d2-14abac4f2e96, 27f4ee33-3d20-44a5-89ff-49e6f2d17a8a. Their a.e. intersections are valid on the unchanged original process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_continuous_all_time
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_boundedVariationOn

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_residual_continuous_monotone_locally_BV
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      Continuous (fun t : ℝ≥0 =>
        (((t : ℝ) * X.drift - X.X t ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) ∧
      Monotone (fun t : ℝ≥0 =>
        (((t : ℝ) * X.drift - X.X t ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        BoundedVariationOn (fun t : ℝ≥0 =>
          (((t : ℝ) * X.drift - X.X t ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)))
          (Icc a b)) := by sorry
