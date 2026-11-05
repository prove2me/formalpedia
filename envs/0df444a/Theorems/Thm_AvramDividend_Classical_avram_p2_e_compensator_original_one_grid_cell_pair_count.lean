-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_one_grid_cell_pair_count
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_one_grid_cell_pair_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:32:34.146587+00:00
-- url     : https://prove2.me/theorems/f914947c-73a9-4fee-b217-ce2b70509000
-- title:
--   Original past-window product equals literal crossing marked-time pair count
-- statement:
--   On the original Lévy path, the product of original past and next-window marked counts equals the literal number of actual negative-band chronological pairs crossing the deterministic grid boundary.
-- source:
--   Source exact first helper 0d0d4845 (window finite-set filter), second helper 6816540b (crossing-pair product cardinal), and actual finite negative-band marked-time theorem e5e6f70b; same original X and no stochastic replacement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_window_count_finset_filter
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_grid_crossing_pair_card

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_one_grid_cell_pair_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (n : ℕ) :
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
    N 0 s * N s t =
      (((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        p.1 ≤ s ∧ s < p.2 ∧ p.2 ≤ t)).card : ℝ≥0∞) := by sorry
