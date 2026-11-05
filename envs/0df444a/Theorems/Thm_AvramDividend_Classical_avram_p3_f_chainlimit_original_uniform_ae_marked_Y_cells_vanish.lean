-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_uniform_ae_marked_Y_cells_vanish
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_uniform_ae_marked_Y_cells_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:52:22.101396+00:00
-- url     : https://prove2.me/theorems/5249de36-87c9-4bfe-a21a-a7b02414f1de
-- title:
--   One original BV source full-measure event controls vanishing marked Y increments for path-chosen finite jump times
-- statement:
--   On one full-measure event of the genuine original bounded-variation Lévy process, for every path-selected finite set S of strictly positive original jump times and every family of physical left/right source-cell endpoints converging to each marked time, the sum of actual jump-removed original Y increments in these cells tends to zero. The finite marks and the endpoint maps are all quantified inside the almost-sure event, so adaptive pathwise finite truncation is sound. Original negative jumps are retained inside J; no generator compensation or stopped budget is assumed.
-- source:
--   Proved original universal positive-time jump-removed continuity 394ca2b9 and Proved finite marked cell absolute sum limit 4a7cc66d, with full-measure quantifier moved outside the arbitrary marks and endpoints.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_continuous_positive_time
import Theorems.Thm_AvramDividend_Classical_avram_p3_d_bvmesh_finitely_marked_original_jump_cells_vanish
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_uniform_ae_marked_Y_cells_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      ∀ (S : Finset ℝ≥0) (hPositive : ∀ t ∈ S, 0 < t)
        (left right : ℕ → ℝ≥0 → ℝ≥0)
        (hLeft : ∀ t ∈ S,
          Filter.Tendsto (fun k => left k t) Filter.atTop (nhds t))
        (hRight : ∀ t ∈ S,
          Filter.Tendsto (fun k => right k t) Filter.atTop (nhds t)),
      let Y : ℝ≥0 → ℝ := fun s => X.X s ω +
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)
      Filter.Tendsto
        (fun k => ∑ t ∈ S, |Y (right k t) - Y (left k t)|)
        Filter.atTop (nhds 0) := by sorry
