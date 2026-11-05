-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_all_mesh_ceiling_pair_card
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_all_mesh_ceiling_pair_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:05:19.5105+00:00
-- url     : https://prove2.me/theorems/efc18d88-37f8-41b1-a4ad-ddc88c4896cc
-- title:
--   All deterministic original Lévy meshes identify bounded Fin-index pair count with literal ceiling pairs
-- statement:
--   For every positive deterministic physical uniform mesh k, and the literal finite negative-band jump-time set of the same Avram original process X on Ω, the generic bounded Fin(k+1) past-times-cell pair count equals the cardinal of pairs with strictly increasing physical Nat.ceil time indices. This is a source-exact all-k pathwise identity, required to transfer P2-E compensated window rate sums to P4-F's eventual-exact chronological pair expectation. Existing results only give a fine-grid existential equality for the full chronological count, which does not supply fixed-k expectations.
-- source:
--   Proved original marked finite jump-times e5e6f70b, their in-range ceiling theorem b329ff6d, generic finite-grid cross-pair cardinal e4059cbe; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_mesh_index_in_range
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_finite_grid_cross_pair_card_identity
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_all_mesh_ceiling_pair_card
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (n k : ℕ) (hk : 0 < k) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let g : ℝ≥0 → Fin (k + 1) := fun u =>
      ⟨min (Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))) k,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
    (∑ i : Fin (k + 1),
      (F.filter (fun u => g u < i)).card *
        (F.filter (fun v => g v = i)).card) =
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card := by sorry
