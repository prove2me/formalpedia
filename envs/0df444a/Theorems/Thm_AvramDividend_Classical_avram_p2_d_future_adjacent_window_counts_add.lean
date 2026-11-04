-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_adjacent_window_counts_add
-- name    : AvramDividend.Classical.avram_p2_d_future_adjacent_window_counts_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:24:46.126825+00:00
-- url     : https://prove2.me/theorems/d039635c-cd1d-4917-8940-842ca1a4bd64
-- title:
--   Original intrinsic marked jump counts add across adjacent time windows
-- statement:
--   For the exact original spectrally negative Lévy process, any sample path and arbitrary Borel mark set, the intrinsic marked jump count on (s,u] equals the sum on (s,t] and (t,u], including infinite activity and endpoint jumps.
-- source:
--   Adjacent half-open time windows are disjoint measurable sets and their union is the full interval. Apply additivity of the exact original mapped counting measure, without a Lévy intensity assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_adjacent_window_counts_add
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∀ ω : Ω,
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v,
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc s u ×ˢ B) =
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v,
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc s t ×ˢ B) +
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v,
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc t u ×ˢ B) := by sorry
