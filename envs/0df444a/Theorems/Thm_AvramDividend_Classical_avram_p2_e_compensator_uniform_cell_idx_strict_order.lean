-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_cell_idx_strict_order
-- name    : AvramDividend.Classical.avram_p2_e_compensator_uniform_cell_idx_strict_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:24:52.756355+00:00
-- url     : https://prove2.me/theorems/c2eb97d6-d0c2-44a5-be8c-61c8d8a6d1e1
-- title:
--   Injective strict-left right-closed uniform cells preserve physical jump-time order
-- statement:
--   On a finite source time set with a half-open uniform cell selector, eventual injectivity of selected cells implies strictly increasing cell indices on strictly increasing physical times.
-- source:
--   Pinned Mathlib natural-number/cast order lemmas and the source half-open uniform cell selector/injectivity pattern in Proved Avram P2-A theorem bd4bfbea. This finite deterministic lemma is used for source chronological pair fibre coverage in P2-E.

import Mathlib

open Set
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_uniform_cell_idx_strict_order
    (F : Finset ℝ≥0) (δ : ℝ≥0) (idx : ℝ≥0 → ℕ)
    (hcell : ∀ u ∈ F,
      (idx u : ℝ≥0) * δ < u ∧
      u ≤ (((idx u + 1 : ℕ) : ℝ≥0) * δ))
    (hinj : Set.InjOn idx (F : Set ℝ≥0)) :
    ∀ u ∈ F, ∀ v ∈ F, u < v → idx u < idx v := by sorry
