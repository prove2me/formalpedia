-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_residual_stieltjes_function
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_residual_stieltjes_function
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:03:32.260465+00:00
-- url     : https://prove2.me/theorems/ab8ff9ee-3cfe-48e8-965b-b4e048626817
-- title:
--   Original BV jump-removed physical drift residual admits a genuine Stieltjes function on the same sample paths
-- statement:
--   Under only the actual original bounded-variation Levy assumptions, almost every physical drift residual path after deleting the genuinely observed negative left jumps is represented exactly by a Mathlib StieltjesFunction on nonnegative clocks. This uses its accepted continuity and monotonicity, so the resulting nonnegative Stieltjes measure can be used in deterministic integration. It does not assert the residual measure is zero.
-- source:
--   Pinned Mathlib 0df444a3 private signature probe of StieltjesFunction.mk: (toFun : R → ℝ) → Monotone toFun → (∀ x, ContinuousWithinAt toFun (Set.Ici x) x) → StieltjesFunction R. Previously Proved source continuity 56ed0b8e... and monotonicity e9d95081... supply the constructor obligations on one original P-full event.

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_continuous_all_time
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_residual_stieltjes_function
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0, ∀ t : ℝ≥0,
      F t = (((t : ℝ) * X.drift - X.X t ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) := by sorry
