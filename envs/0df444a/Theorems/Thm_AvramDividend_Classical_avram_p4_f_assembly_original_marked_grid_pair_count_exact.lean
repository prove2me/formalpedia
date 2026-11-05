-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_grid_pair_count_exact
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_marked_grid_pair_count_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:52:15.292198+00:00
-- url     : https://prove2.me/theorems/0f901c60-a31e-46f6-b4c8-f72360b89b1b
-- title:
--   Exact original Lévy chronological jump pair cardinal equals a finite uniform-grid past-times-cell count
-- statement:
--   At every original negative-band finite-mark jump path with positive horizon, a fine finite uniform grid yields equality of the physical chronological ordered-pair count and a sum of finite past-event times current-cell counts. The mesh map is a total bounded Fin index, equal to the true ceiling index on the original source marked-time set. Uses only Proved source marked-time index and abstract finite-grid pair count lemmas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pair_strict_mesh_index
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_mesh_index_in_range
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_finite_grid_cross_pair_card_identity
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_marked_grid_pair_count_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k : ℕ, 0 < k ∧
      let g : ℝ≥0 → Fin (k + 1) := fun u =>
        ⟨min (Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))) k,
          Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
      (∑ i : Fin (k + 1),
        (F.filter (fun u => g u < i)).card *
          (F.filter (fun v => g v = i)).card) =
        ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by sorry
