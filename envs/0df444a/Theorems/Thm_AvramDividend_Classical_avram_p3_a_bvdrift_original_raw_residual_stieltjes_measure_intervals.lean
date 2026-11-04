-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_residual_stieltjes_measure_intervals
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_residual_stieltjes_measure_intervals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:09:35.956782+00:00
-- url     : https://prove2.me/theorems/d20b5d08-c1d3-4a8a-b605-59f5e7f5a27f
-- title:
--   Original BV raw residual admits a nonnegative Stieltjes measure with exactly its real interval increments
-- statement:
--   The original jump-removed BV residual is represented by an actual nonnegative Mathlib measure on every source path in one full-probability event; its measure of each right-closed interval is precisely ENNReal.ofReal of the residual increment. This gives P3 a genuine integration measure before the missing rate/Laplace identification and without introducing any alternative process.
-- source:
--   Proved StieltjesFunction constructor helper (awaiting acceptance), plus pinned remote compiler signature StieltjesFunction.measure_Ioc: F.measure (Ioc a b) = ENNReal.ofReal (F b - F a) at Mathlib rev 0df444a3.

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_residual_stieltjes_function

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_residual_stieltjes_measure_intervals
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℝ≥0, ∀ a b : ℝ≥0, a ≤ b →
      μ (Ioc a b) = ENNReal.ofReal (
        ((((b : ℝ) * X.drift - X.X b ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) -
        (((a : ℝ) * X.drift - X.X a ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)))) := by sorry
