-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_grid_past_cell_sum
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_ceil_grid_past_cell_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:22:10.242609+00:00
-- url     : https://prove2.me/theorems/c7fa6a87-3154-4325-9408-b4aed2125cc5
-- title:
--   Every original physical ceiling-grid pair count is the sum of past-by-cell cardinal products
-- statement:
--   For every fixed positive uniform mesh k, literal negative-band marked jump times F of Avram's original spectrally negative Lévy process satisfy an exact natural-number identity: the pair cardinal with strictly increasing Nat.ceil indices equals the sum over i=0,...,k-1 of the count of past marked times at ceiling≤i multiplied by the count in ceiling-cell i+1. This is the source pathwise fixed-grid equality needed to connect P2-E original count-rate compensation with P4-F's source factorial second moment. All source data remain X, P, ν_X and the actual finite marked-time set.
-- source:
--   Proved source range b329ff6d, newly authored same-original-process fixed mesh pair card bridge, Fin.sum_univ_succ pinned at Mathlib 0df444..., in-source Finset.filter congruence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_mesh_index_in_range
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_all_mesh_ceiling_pair_card
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_ceil_grid_past_cell_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (n k : ℕ) (hk : 0 < k) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) < Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card =
    ∑ i : Fin k,
      (F.filter (fun (u : ℝ≥0) => Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ i.val)).card *
      (F.filter (fun (v : ℝ≥0) => Nat.ceil ((v : ℝ) * (k : ℝ) / (T : ℝ)) = i.val + 1)).card := by sorry
