-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_grid_pair_lintegral_upper_bound
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_grid_pair_lintegral_upper_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:50:11.41832+00:00
-- url     : https://prove2.me/theorems/164590db-ac31-446b-9294-6e43d8268449
-- title:
--   Original finite-grid marked-count pair expectation bounded by true chronological pair mean
-- statement:
--   Taking original probability expectations of the proved pointwise finite-grid source negative-band chronological pair bound yields an ENNReal inequality against the actual physical source chronological pair count.
-- source:
--   Source-exact public Proved pointwise original negative-band marked-count grid pair sum bound 71f59696, followed by pinned Mathlib MeasureTheory.lintegral_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_grid_pair_sum_le_total

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_original_grid_pair_lintegral_upper_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (m : ℕ) (s t : Fin m → ℝ≥0) (n : ℕ)
    (hst : ∀ i, s i ≤ t i) (htT : ∀ i, t i ≤ T)
    (hdisj : ∀ i j : Fin m, i ≠ j →
      Disjoint (Ioc (s i) (t i)) (Ioc (s j) (t j))) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    (∫⁻ ω, ∑ i : Fin m, N 0 (s i) ω * N (s i) (t i) ω ∂P) ≤
      ∫⁻ ω, (((F ω ×ˢ F ω).filter
        (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℝ≥0∞) ∂P := by sorry
