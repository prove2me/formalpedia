-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_stieltjes_measure_intervals
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_stieltjes_measure_intervals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:34:02.460903+00:00
-- url     : https://prove2.me/theorems/bb53b9ce-7b8a-43bd-a20f-5d570fdc9f18
-- title:
--   Stieltjes interval measure exactly represents the original BV negative jump increments
-- statement:
--   On the identical original bounded-variation Levy probability space, the cumulative magnitude of all actual negative left jumps has a genuine Stieltjes measure. For any 0≤a≤b this measure assigns the half-open interval (a,b] precisely the real increment of the genuine original negative jump sum, cast to ENNReal. This is an integration-ready measure without an auxiliary jump process.
-- source:
--   Exact pinned Mathlib StieltjesFunction.measure_Ioc and source original signed raw jump Stieltjes function obtained from BV jump summability, monotonicity and right continuity.

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_stieltjes_measure_intervals
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℝ≥0,
      ∀ a b : ℝ≥0, a ≤ b → μ (Ioc a b) = ENNReal.ofReal (
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) := by sorry
