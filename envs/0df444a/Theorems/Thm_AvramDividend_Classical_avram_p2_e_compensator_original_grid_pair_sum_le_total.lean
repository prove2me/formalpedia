-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_grid_pair_sum_le_total
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_grid_pair_sum_le_total
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:42:25.229799+00:00
-- url     : https://prove2.me/theorems/71f59696-f5f8-463b-93e4-3db9ccced6ec
-- title:
--   Original finite-grid jump pair sum bounded by all source chronological pairs
-- statement:
--   The actual original negative-band past/future rectangle pair-product sum over disjoint physical time cells is bounded pointwise by the total number of source chronological negative-band jump pairs.
-- source:
--   Accepted original one-cell source pair count and disjoint finite-grid pair-card inequality, both proved from original negative marked finite times; source second factorial moment d938e9a5 requires this pointwise inequality for Fatou.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_one_grid_cell_pair_count
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_disjoint_grid_pair_card_le

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_original_grid_pair_sum_le_total
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (m : ℕ) (s t : Fin m → ℝ≥0) (n : ℕ)
    (hst : ∀ i, s i ≤ t i) (htT : ∀ i, t i ≤ T)
    (hdisj : ∀ i j : Fin m, i ≠ j →
      Disjoint (Ioc (s i) (t i)) (Ioc (s j) (t j))) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → ℝ≥0∞ := fun a b =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    (∑ i : Fin m, N 0 (s i) * N (s i) (t i)) ≤
      (((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℝ≥0∞) := by sorry
