-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_occupied_grid_card_le_source_finset_card
-- name    : AvramDividend.Classical.avram_wave7_06_occupied_grid_card_le_source_finset_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:06:13.658211+00:00
-- url     : https://prove2.me/theorems/0b6de847-b781-4eab-9a2d-dec119679f3f
-- title:
--   Occupied original marked-time grid cells are bounded by the finite source jump count
-- statement:
--   For the finite set F of actual marked jump times and any finite family of disjoint time cells indexed by I, if every time belongs to at most one cell then the number of occupied cells cannot exceed the number of source jump times. This is the dominating random-variable inequality needed for the original-process occupied-grid L¹ limit under its ν-rate.
-- source:
--   Exact finite source marked-time cardinal bound; uses pinned Finset.card_le_card_of_injOn, no auxiliary process.

import Mathlib
open Set
open scoped NNReal

theorem AvramDividend.Classical.avram_wave7_06_occupied_grid_card_le_source_finset_card
    (F : Finset ℝ≥0) (I : Finset ℕ)
    (R : ℝ≥0 → ℕ → Prop)
    (A : Finset ℕ)
    (hA : ∀ i, i ∈ A ↔ i ∈ I ∧ ∃ u ∈ F, R u i)
    (hIndexUnique : ∀ u ∈ F, ∀ i ∈ I, ∀ j ∈ I,
      R u i → R u j → i = j) :
    A.card ≤ F.card := by sorry
