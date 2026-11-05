-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pair_strict_mesh_index
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_marked_pair_strict_mesh_index
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:33:28.342774+00:00
-- url     : https://prove2.me/theorems/5662c473-938b-4d42-8b91-5d0b13c23297
-- title:
--   Every pair of original separated marked jump times has strictly ordered fine uniform-mesh indices
-- statement:
--   For the literal original negative-band jump-time finset on (0,T] with positive T, one positive integer k gives a strictly increasing ceiling mesh index to every distinct ordered pair of source jump times. Derived from the already Proved original uniform grid separation, without auxiliary processes or assumptions about probability moments.

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pairs_uniform_grid_scale
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_marked_pair_strict_mesh_index
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k : ℕ, 0 < k ∧
      ∀ u ∈ F, ∀ v ∈ F, u < v →
        Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((v : ℝ) * (k : ℝ) / (T : ℝ)) := by sorry
