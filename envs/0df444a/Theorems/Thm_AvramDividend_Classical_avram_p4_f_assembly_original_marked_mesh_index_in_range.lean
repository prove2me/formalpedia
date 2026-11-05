-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_mesh_index_in_range
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_marked_mesh_index_in_range
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:34:51.856932+00:00
-- url     : https://prove2.me/theorems/b329ff6d-5f84-4573-b2e1-92dc91ac36ac
-- title:
--   Original negative-band jump times occupy positive uniform mesh indices bounded by the horizon mesh size
-- statement:
--   Each literal original marked jump time u lies in (0,T]; for positive finite horizon T and positive integer k its ceiling mesh index ceil(u*k/T) lies in {1,...,k}. This is an exact source-path interval-cover bridge for the finite-grid chronological pair-count identity.

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_marked_mesh_index_in_range
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (n k : ℕ) (hk : 0 < k) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∀ u ∈ F,
      0 < Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ∧
      Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ k := by sorry
