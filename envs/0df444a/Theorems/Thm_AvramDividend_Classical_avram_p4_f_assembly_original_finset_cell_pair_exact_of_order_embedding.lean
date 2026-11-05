-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finset_cell_pair_exact_of_order_embedding
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_finset_cell_pair_exact_of_order_embedding
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:31:12.251056+00:00
-- url     : https://prove2.me/theorems/a4ec8871-8ca9-4faa-a6e4-f849793684b1
-- title:
--   Original chronological marked jump pairs equal cumulative-past times cell occupancy for an order-faithful finite grid
-- statement:
--   For the literal finite set F of negative-band marked jump times of the original Lévy process X at horizon T, and a finite cell-index map g that reflects the strict chronological ordering of all actual times in F, the exact source chronological pair cardinality equals the finite sum over cells of the number of earlier marked times times the number in the current cell. The source identity hF and the order-reflection premise are explicit, to be discharged using the proved original finite-time grid separation and exact source cell-count representation. This is the deterministic pair-counting half of the original second-factorial moment d938e9a5.
-- source:
--   Proved source-specific ordered-pair count as sum of past marked source times 1aea4cfb; Finset.filter and finite double-sum commutation; mesh/order-reflection must be discharged separately by Proved original marked pair grid scale d4f9ea74 and fine-cell exclusion f6039862.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_source_ordered_pairs_as_past_counts
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_finset_cell_pair_exact_of_order_embedding
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ)
    (F : Finset ℝ≥0) (hF : F = (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset)
    (k : ℕ) (g : ℝ≥0 → Fin k)
    (horder : ∀ u ∈ F, ∀ v ∈ F, (g u < g v) ↔ u < v) :
    (∑ i : Fin k,
      (F.filter (fun u => g u < i)).card *
      (F.filter (fun v => g v = i)).card) =
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by sorry
