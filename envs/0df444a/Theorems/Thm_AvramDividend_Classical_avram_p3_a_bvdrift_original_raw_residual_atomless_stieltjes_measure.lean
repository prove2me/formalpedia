-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_residual_atomless_stieltjes_measure
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_residual_atomless_stieltjes_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:11:10.106185+00:00
-- url     : https://prove2.me/theorems/14795a0f-76ca-4838-b813-94403f0843b2
-- title:
--   Original BV raw residual induces a non-atomic positive Stieltjes measure with exact interval masses
-- statement:
--   For almost every original BV Levy path, the continuous increasing actual negative-jump-removed physical drift residual generates a nonnegative Stieltjes measure. The measure has exactly the residual increments on all right-closed intervals, and every singleton has zero mass. This identifies the residual as a possible continuous finite-variation Stieltjes integrator without claiming it vanishes.
-- source:
--   Previously Proved original continuity and (pending) original StieltjesFunction representation, pinned Mathlib StieltjesFunction.measure_Ioc and StieltjesFunction.measure_singleton, and ContinuousWithinAt.leftLim_eq.

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_residual_stieltjes_function
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_continuous_all_time

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_residual_atomless_stieltjes_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℝ≥0,
      (∀ a b : ℝ≥0, a ≤ b →
        μ (Ioc a b) = ENNReal.ofReal (
          ((((b : ℝ) * X.drift - X.X b ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) -
          (((a : ℝ) * X.drift - X.X a ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))))) ∧
      (∀ a : ℝ≥0, μ {a} = 0) := by sorry
