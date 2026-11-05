-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_eventual_uniform_grid_pair_products
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_eventual_uniform_grid_pair_products
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:31:27.338994+00:00
-- url     : https://prove2.me/theorems/3d950ade-6824-4682-97b6-c7e20de0e5a0
-- title:
--   Original physical negative-jump chronological pair count equals fine-grid marked-jump products eventually
-- statement:
--   For the actual original spectrally negative Lévy path, the physical finite-grid marked-jump past/future product sum is eventually identical to the exact original chronological negative-band pair count in the extended nonnegative reals.
-- source:
--   Composition of the verified source exact eventual physical grid pair-card helper 27009 and the original source uniform-grid marked jump product/card identity 27014 (awaiting terminal verdict).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_eventual_uniform_grid_pair_card
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_uniform_grid_pair_sum_card

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_original_eventual_uniform_grid_pair_products
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∀ᶠ k : ℕ in Filter.atTop,
      (let s : Fin (k + 1) → ℝ≥0 := fun i =>
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
       ∑ i : Fin (k + 1), N 0 (s i) * N (s i) (t i)) =
        (((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℝ≥0∞) := by sorry
