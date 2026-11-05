-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_cell_chronological_pair_cover
-- name    : AvramDividend.Classical.avram_p2_e_compensator_uniform_cell_chronological_pair_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:55:59.967347+00:00
-- url     : https://prove2.me/theorems/2b0f636a-73f4-40bc-a47f-35d5af8f22ba
-- title:
--   Chronological source finite-time pairs equal the union of uniform past-future crossing fibres
-- statement:
--   Given half-open uniform cell selections of a finite set of original physical times, with all selected indices inside the grid and injective, every ordered time pair belongs to the crossing fibre of its second time's cell, and conversely.
-- source:
--   Proved P2-E ordered pair fibre helper, Finset.mem_product, Finset.mem_filter and Finset.mem_biUnion. Intended for the literal original negative-band jump-time F and Fatou second-factorial moment.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_cell_ordered_pair_fibre

open Set AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_uniform_cell_chronological_pair_cover
    (F : Finset ℝ≥0) (δ : ℝ≥0) (m : ℕ) (idx : ℝ≥0 → ℕ)
    (hidx : ∀ u ∈ F, idx u < m)
    (hcell : ∀ u ∈ F,
      (idx u : ℝ≥0) * δ < u ∧
      u ≤ (((idx u + 1 : ℕ) : ℝ≥0) * δ))
    (hinj : Set.InjOn idx (F : Set ℝ≥0)) :
    (F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2) =
      (Finset.univ : Finset (Fin m)).biUnion (fun i =>
        (F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
          p.1 ≤ (i.val : ℝ≥0) * δ ∧
          (i.val : ℝ≥0) * δ < p.2 ∧
          p.2 ≤ (((i.val + 1 : ℕ) : ℝ≥0) * δ))) := by sorry
