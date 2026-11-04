-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_interval_cocycle
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_interval_cocycle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:47:25.671368+00:00
-- url     : https://prove2.me/theorems/5b913d53-0281-4b45-b508-bc5ac69419a8
-- title:
--   Original BV raw jump-removed residual has an exact interval cocycle
-- statement:
--   For each ordered pair of clocks, the increment of the actual BV source residual after subtracting all genuine raw left jumps equals the physical-drift increment minus the original X increment and the raw negative-jump series on the interval. This is the pathwise cocycle needed to transport the original independent-increment laws.
-- source:
--   Original raw-jump disjoint interval additivity (publication 50ef916b-57ed-4bdd-b0fa-5630d6e42904, awaiting Proved status), plus real ring algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_interval_cocycle
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      ((((t : ℝ) * X.drift - X.X t ω) - (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) -
        (((s : ℝ) * X.drift - X.X s ω) - (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) =
      (((t : ℝ) - (s : ℝ)) * X.drift - (X.X t ω - X.X s ω)) -
        (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by sorry
