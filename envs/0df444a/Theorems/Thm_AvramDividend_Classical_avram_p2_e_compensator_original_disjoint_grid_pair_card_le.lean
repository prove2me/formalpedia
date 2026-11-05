-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_disjoint_grid_pair_card_le
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_disjoint_grid_pair_card_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:35:51.931969+00:00
-- url     : https://prove2.me/theorems/8f025ae7-340c-4c41-93af-1a8673255b27
-- title:
--   Original negative-band chronological grid crossing-pair count bounded by all actual pairs
-- statement:
--   For the actual original negative-band jump-time Finset, chronological crossing-pair counts over pairwise disjoint half-open deterministic grid cells sum to at most the total chronological pair cardinal.
-- source:
--   The actual original finite negative-band marked-time set e5e6f70b, source pair target d938e9a5, pinned finite-set disjointness/cardinality identities Finset.card_biUnion and Finset.card_le_card. Disjointness assumption explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_original_disjoint_grid_pair_card_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (m : ℕ) (s t : Fin m → ℝ≥0) (n : ℕ)
    (hdisj : ∀ i j : Fin m, i ≠ j →
      Disjoint (Ioc (s i) (t i)) (Ioc (s j) (t j))) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let C : Fin m → Finset (ℝ≥0 × ℝ≥0) := fun i =>
      (F ×ˢ F).filter (fun p => p.1 ≤ s i ∧ s i < p.2 ∧ p.2 ≤ t i)
    (∑ i, (C i).card) ≤
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by sorry
