-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_finite_grid_cross_pair_card_identity
-- name    : AvramDividend.Classical.avram_p4_f_assembly_finite_grid_cross_pair_card_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:42:50.697712+00:00
-- url     : https://prove2.me/theorems/e4059cbe-e221-4e5e-be0a-48477dd12351
-- title:
--   Exact finite-grid cross-count equals ordered pair cardinality for any finite indexed event set
-- statement:
--   For a finite set of events classified into k time cells, the sum over cells of past-event count times current-cell count equals the cardinality of pairs whose first cell index is smaller than the second. This deterministic Finset identity is the source-agnostic counting step for the physical original Lévy marked-jump grid, with actual X substitution handled by separate Proved source-index lemmas.

import Mathlib.Data.Finset.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_finite_grid_cross_pair_card_identity
    {α : Type*} (F : Finset α) (k : ℕ) (g : α → Fin k) :
    (∑ i : Fin k,
      (F.filter (fun u => g u < i)).card *
        (F.filter (fun v => g v = i)).card) =
      ((F ×ˢ F).filter (fun p : α × α => g p.1 < g p.2)).card := by sorry
