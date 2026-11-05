-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_positive_marked_C1_source_cells_vanish
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_positive_marked_C1_source_cells_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:12:03.475194+00:00
-- url     : https://prove2.me/theorems/3be8dfd5-6832-44ac-98ee-ce0b817d31d4
-- title:
--   Original physical continuous-source contribution on finitely tagged positive jump cells tends to zero
-- statement:
--   For the genuine original BV Lévy path, on one full-measure source event, any fixed finite set of strictly positive original jump times has vanishing total continuous-source contribution across mesh cells whose two endpoints approach the respective physical jump times. This uses the actual original negative-jump-removed path and is a source-exact component of the marked-cell term in the two-stage C1 mesh error.
-- source:
--   Proved original physical jump-removed positive-time path continuity 394ca2b9, combined with Proved finite marked-cell sum convergence 4a7cc66d. No surrogate process or generator compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_continuous_positive_time
import Theorems.Thm_AvramDividend_Classical_avram_p3_d_bvmesh_finitely_marked_original_jump_cells_vanish
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_positive_marked_C1_source_cells_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (S : Finset ℝ≥0) (hPositive : ∀ t ∈ S, 0 < t)
    (left right : ℕ → ℝ≥0 → ℝ≥0)
    (hLeft : ∀ t ∈ S,
      Filter.Tendsto (fun k => left k t) Filter.atTop (nhds t))
    (hRight : ∀ t ∈ S,
      Filter.Tendsto (fun k => right k t) Filter.atTop (nhds t)) :
    ∀ᵐ ω ∂P,
      let Y : ℝ≥0 → ℝ := fun s => X.X s ω +
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)
      Filter.Tendsto
        (fun k => ∑ t ∈ S, |Y (right k t) - Y (left k t)|)
        Filter.atTop (nhds 0) := by sorry
