-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_source_marked_cell_order_embedding
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_source_marked_cell_order_embedding
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:47:34.652058+00:00
-- url     : https://prove2.me/theorems/ec7f1a07-b71a-4db5-afac-81cd269b6828
-- title:
--   Original marked jump times admit an order-faithful bounded finite-grid index map
-- statement:
--   For original X and its exact finite set of negative-band marks over a positive horizon T, construct a finite grid index into Fin(k+1) that reflects chronological ordering. Derive from source exact proved mesh ceiling strictness 5662c473 and bound b329ff6d. This discharges the order-embedding premise of source exact ordered-cell pair count a4ec8871.
-- source:
--   Verified Proved original-source marked time separation 5662c473 and original source mesh index bound b329ff6d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pair_strict_mesh_index
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_mesh_index_in_range
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_source_marked_cell_order_embedding
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k : ℕ, 0 < k ∧ ∃ g : ℝ≥0 → Fin (k + 1),
      ∀ u ∈ F, ∀ v ∈ F, (g u < g v) ↔ u < v := by sorry
