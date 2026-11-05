-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pairs_all_finer_mesh_indices
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_marked_pairs_all_finer_mesh_indices
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:50:12.376716+00:00
-- url     : https://prove2.me/theorems/c495c7e6-c91c-4765-8740-db9cdc832848
-- title:
--   All sufficiently fine uniform meshes strictly separate every original negative-band chronological jump pair
-- statement:
--   For the literal finite marked negative-jump time set of the original Lévy path at positive horizon T, there exists one positive k0 such that every finer integer mesh k≥k0 assigns strictly ordered ceiling indices to every chronological pair. This eventwise eventual separation, not grid monotonicity, is the exact pathwise stabilisation premise for a Fatou-based second-factorial-moment proof.

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pairs_uniform_grid_scale
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_marked_pairs_all_finer_mesh_indices
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k₀ : ℕ, 0 < k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
      ∀ u ∈ F, ∀ v ∈ F, u < v →
        Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((v : ℝ) * (k : ℝ) / (T : ℝ)) := by sorry
