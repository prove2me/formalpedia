-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pairs_unit_mesh_bracket
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_marked_pairs_unit_mesh_bracket
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:07:56.672123+00:00
-- url     : https://prove2.me/theorems/3a8a89ad-c34b-4065-a2ff-0e0f50a46cbc
-- title:
--   Every pair of actual original negative-band jumps has a separating common unit-mesh boundary
-- statement:
--   For any original spectrally negative Lévy sample path and finite horizon, one positive integer mesh resolution k simultaneously separates every chronological pair u<v in the actual finite negative-band marked jump-time set by a rational time i/k with u≤i/k<v. This is an exact-source pathwise finite-grid exhaustion input to the original second factorial moment.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_times_chronological_gap
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_marked_pairs_unit_mesh_bracket
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k : ℕ, 0 < k ∧
      ∀ u ∈ F, ∀ v ∈ F, u < v →
        ∃ i : ℕ, (u : ℝ) ≤ (i : ℝ) / (k : ℝ) ∧
          (i : ℝ) / (k : ℝ) < (v : ℝ) := by sorry
