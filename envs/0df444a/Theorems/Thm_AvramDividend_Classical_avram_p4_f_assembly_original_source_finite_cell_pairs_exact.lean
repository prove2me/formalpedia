-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_source_finite_cell_pairs_exact
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_source_finite_cell_pairs_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:50:28.641728+00:00
-- url     : https://prove2.me/theorems/7cf8ae12-ce96-4308-8bc5-3cdd945eff4f
-- title:
--   Actual original negative-band chronological pair count equals one finite source grid cross-cell sum
-- statement:
--   For every same-original-process finite marked-time set F at positive horizon, construct a finite grid index map that exactly represents the chronological source pair count as past marked times times current-cell marked times. This composes the independent source order embedding ec7f1a07 with exact source finite-cell pair accounting a4ec8871. It is an acyclic graph bridge toward the second-factorial source expectation d938e9a5; source stochastic expectation and stopped Ito-Meyer remain separate.
-- source:
--   Exact source-grid order embedding ec7f1a07 and exact source pair sum a4ec8871, both authored independently from the same X and F.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_source_marked_cell_order_embedding
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finset_cell_pair_exact_of_order_embedding
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_source_finite_cell_pairs_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k : ℕ, 0 < k ∧ ∃ g : ℝ≥0 → Fin (k + 1),
      (∑ i : Fin (k + 1),
        (F.filter (fun u => g u < i)).card *
        (F.filter (fun v => g v = i)).card) =
        ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by sorry
