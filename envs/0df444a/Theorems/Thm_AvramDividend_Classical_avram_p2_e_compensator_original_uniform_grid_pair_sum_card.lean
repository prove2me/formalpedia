-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_uniform_grid_pair_sum_card
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_uniform_grid_pair_sum_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:14:10.535375+00:00
-- url     : https://prove2.me/theorems/7d8b6066-014f-49ba-84f6-af9f088125dd
-- title:
--   Original marked-jump uniform grid product sum equals the literal crossing-pair cardinality sum
-- statement:
--   For the actual original Lévy process, the ENNReal sum of products of marked past and future negative-jump counts over the physical uniform grid is exactly the Nat-to-ENNReal cast of the sum of literal chronological crossing-pair cardinalities of the original jump-time set.
-- source:
--   Accepted original one-cell marked-jump product/cardinality identity f914947c and accepted physical uniform-grid time bounds 38bdd935, combined by finite sum and Nat-to-ENNReal casts.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_one_grid_cell_pair_count
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_grid_cell_bounds

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_original_uniform_grid_pair_sum_card
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (k n : ℕ) :
    let s : Fin (k + 1) → ℝ≥0 := fun i =>
      (i.val : ℝ≥0) * (T / ((k : ℝ≥0) + 1))
    let t : Fin (k + 1) → ℝ≥0 := fun i =>
      (((i.val + 1 : ℕ) : ℝ≥0) * (T / ((k : ℝ≥0) + 1)))
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
    (∑ i : Fin (k + 1), N 0 (s i) * N (s i) (t i)) =
      ((∑ i : Fin (k + 1),
        ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
          p.1 ≤ s i ∧ s i < p.2 ∧ p.2 ≤ t i)).card : ℕ) : ℝ≥0∞) := by sorry
