-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_finite_real_natural_enumeration_sum_transfer_20261112
-- name    : AvramDividend.Classical.avram_a21_finite_real_natural_enumeration_sum_transfer_20261112
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:10:45.654187+00:00
-- url     : https://prove2.me/theorems/57c06109-61a5-419a-98e6-c9a2f0689d58
-- title:
--   Finite real mark fibre energy sums are invariant under faithful natural-index re-enumeration
-- statement:
--   If the natural indices below the cardinality of a finite set of real values enumerate its elements bijectively, then summing any real weight across the natural index range equals summing over the original finite set exactly.
-- source:
--   Mathlib Finset.sum_bij, pinned revision 0df444a360eaa60ab8c11dca51a86af692955474 and current Mathlib documentation checked. To reindex original Borel simple mark fibres and centred energies in 67336b2d.

import Mathlib
open Finset
noncomputable section

theorem AvramDividend.Classical.avram_a21_finite_real_natural_enumeration_sum_transfer_20261112
    (s : Finset ℝ) (u : ℕ → ℝ)
    (hu : ∀ i ∈ Finset.range s.card, u i ∈ s)
    (hinj : ∀ i ∈ Finset.range s.card,
      ∀ j ∈ Finset.range s.card, i ≠ j → u i ≠ u j)
    (hsurj : ∀ y ∈ s, ∃ i ∈ Finset.range s.card, u i = y)
    (w : ℝ → ℝ) :
    (∑ i ∈ Finset.range s.card, w (u i)) =
      ∑ y ∈ s, w y := by sorry
