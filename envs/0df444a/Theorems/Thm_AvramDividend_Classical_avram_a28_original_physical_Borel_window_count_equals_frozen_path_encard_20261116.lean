-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a28_original_physical_Borel_window_count_equals_frozen_path_encard_20261116
-- name    : AvramDividend.Classical.avram_a28_original_physical_Borel_window_count_equals_frozen_path_encard_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:46:40.570629+00:00
-- url     : https://prove2.me/theorems/e617f90e-f389-48a1-9ddc-746ba2839e65
-- title:
--   Original physical marked Borel window count equals the same marked count on the original path frozen at the right endpoint
-- statement:
--   For every actual original Levy path and Borel mark set, the genuine physical B-marked jump count on (s,T] equals the cardinality of nonzero B-marked jumps of the same path frozen at T. Original and frozen jump marks agree at all positive times through T, with no changes to the probability space. Derived from the proved source rectangle encard identity and exact frozen left-limit equality.
-- source:
--   Proved original rectangle encard f6336d40 and frozen left-limits 8e873bf7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a28_original_physical_Borel_window_count_equals_frozen_path_encard_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s T ×ˢ B) =
      ({u : ℝ≥0 | s < u ∧ u ≤ T ∧
        X.X (min u T) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u ≠ 0 ∧
        X.X (min u T) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u ∈ B}).encard := by sorry
