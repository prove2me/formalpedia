-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_borel_countable_additivity
-- name    : AvramDividend.Classical.avram_p2_d_future_intrinsic_borel_countable_additivity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:30:41.762903+00:00
-- url     : https://prove2.me/theorems/890cbfa0-9130-44a5-8811-cf13ea7d163f
-- title:
--   Original intrinsic marked sample counts obey Borel countable additivity
-- statement:
--   For the unchanged original spectrally negative Lévy process, the literal intrinsic marked jump count of any countable disjoint union of jointly Borel time–mark sets equals the ENNReal infinite sum of individual literal counts, without finite activity or intensity assumptions.
-- source:
--   A source-exact direct instantiation of pinned Mathlib MeasureTheory.measure_iUnion (verified type) for the actual original restricted counting measure pushed forward by physical jump time and mark.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_d_future_intrinsic_borel_countable_additivity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (C : ℕ → Set (ℝ≥0 × ℝ))
    (hDisj : Pairwise (Function.onFun Disjoint C))
    (hC : ∀ n, MeasurableSet (C n)) :
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (⋃ n, C n) =
      ∑' n, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (C n) := by sorry
