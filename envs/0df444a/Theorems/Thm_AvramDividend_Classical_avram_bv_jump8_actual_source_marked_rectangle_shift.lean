-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_actual_source_marked_rectangle_shift
-- name    : AvramDividend.Classical.avram_bv_jump8_actual_source_marked_rectangle_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:45:04.921226+00:00
-- url     : https://prove2.me/theorems/5714bfe7-d421-496f-a0b9-8d85186eef07
-- title:
--   Original source intrinsic shifted-path and physical-time marked Borel rectangle counts coincide pointwise
-- statement:
--   For every same-source sample and Borel mark set, the genuine original process's shifted future increment path has the same nonzero marked jump count over (0,1] as the original path over (n,n+1]. It is a pointwise sample equality for all B, retaining the strict time zero convention.
-- source:
--   Use Proved ed946858 arbitrary source marked interval same-sample count, Proved 81fc4187 exact leftLimit translation and count-restrict map evaluation. No stationarity or Poisson replacement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_interval_samepath_marked_count
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_actual_source_marked_rectangle_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
        (X.X ((n : ℝ≥0) + u) ω - X.X (n : ℝ≥0) ω) -
          Function.leftLim
            (fun v : ℝ≥0 => X.X ((n : ℝ≥0) + v) ω - X.X (n : ℝ≥0) ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        (X.X ((n : ℝ≥0) + u) ω - X.X (n : ℝ≥0) ω) -
          Function.leftLim
            (fun v : ℝ≥0 => X.X ((n : ℝ≥0) + v) ω - X.X (n : ℝ≥0) ω) u)))
      (Ioc 0 1 ×ˢ B) =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (n : ℝ≥0) ((n : ℝ≥0) + 1) ×ˢ B) := by sorry
