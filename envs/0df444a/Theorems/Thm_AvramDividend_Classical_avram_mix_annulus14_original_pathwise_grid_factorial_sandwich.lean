-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus14_original_pathwise_grid_factorial_sandwich
-- name    : AvramDividend.Classical.avram_mix_annulus14_original_pathwise_grid_factorial_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:17:36.913097+00:00
-- url     : https://prove2.me/theorems/da4560bb-011c-4c48-9358-963904a8d979
-- title:
--   Original physical annulus factorial count bounded by chronological cross and full-cutoff cell collisions
-- statement:
--   For any monotone physical time grid covering the horizon, the factorial jump count of the original negative annulus lies between the strictly chronological cross-cell pair count and that count plus the full-cutoff same-cell factorial collisions. Every count is identified with a cardinal of original physical jump times, retaining strict lower and closed upper mark endpoints.
-- source:
--   Root-connected source identity and combinatorics: Proved fa9ef32b window-filter annulus cardinal, 09bdd280 marked-count Ioc time grid telescoping, 43e4d0f0 generic factorial collision sandwich. Consumer d924a79e and factorial parent 6ea0212e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus14_original_window_filter_card
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_marked_count_grid_telescoping
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_finite_grid_factorial_collision_sandwich
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus14_original_pathwise_grid_factorial_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hZero : grid 0 = 0) (q : ℕ) (hT : grid q = T) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T m).toFinset
    let a : ℕ → ℕ := fun i =>
      (F.filter (fun u => grid i < u ∧ u ≤ grid (i + 1) ∧
        -(1 / ((n : ℝ) + 1)) <
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)).card
    let b : ℕ → ℕ := fun i =>
      (F.filter (fun u => grid i < u ∧ u ≤ grid (i + 1))).card
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : ℝ := (((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal
    let H : ℝ := 2 * (∑ i ∈ Finset.range q,
      (∑ j ∈ Finset.range i, (a j : ℝ)) * (a i : ℝ))
    H ≤ N * (N - 1) ∧
      N * (N - 1) ≤ H +
        ∑ i ∈ Finset.range q, (b i : ℝ) * ((b i : ℝ) - 1) := by sorry
