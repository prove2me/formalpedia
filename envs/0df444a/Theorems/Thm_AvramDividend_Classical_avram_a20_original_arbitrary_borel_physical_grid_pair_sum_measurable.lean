-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_arbitrary_borel_physical_grid_pair_sum_measurable
-- name    : AvramDividend.Classical.avram_a20_original_arbitrary_borel_physical_grid_pair_sum_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:14:05.96606+00:00
-- url     : https://prove2.me/theorems/6a10d214-9452-4842-99d4-9bb12f4cc1ce
-- title:
--   All arbitrary Borel original-source chronological finite-grid marked-count product sums are measurable
-- statement:
--   For the genuine original spectrally negative Lévy process, an arbitrary measurable Borel jump-mark set B and any finite family of deterministic physical time intervals, the samplewise sum of past marked counts times subsequent marked-cell counts is measurable on the original sample space. Reuses the already Proved original physical marked-rectangle measurability theorem for each Borel cell, then multiplies and sums finitely. The proof generalises the accepted fixed cutoff finite-grid measurability result. This is the precise source measurability premise for almost-sure eventual-grid Fatou and Borel chronological-pair expectations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_marked_rectangle_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_arbitrary_borel_physical_grid_pair_sum_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m : ℕ) (s t : Fin m → ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    Measurable (fun ω => ∑ i : Fin m,
      N 0 (s i) ω * N (s i) (t i) ω) := by sorry
