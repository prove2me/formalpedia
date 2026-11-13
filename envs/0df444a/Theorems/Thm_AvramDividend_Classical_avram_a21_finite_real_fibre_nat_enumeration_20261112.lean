-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_finite_real_fibre_nat_enumeration_20261112
-- name    : AvramDividend.Classical.avram_a21_finite_real_fibre_nat_enumeration_20261112
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:08:13.920199+00:00
-- url     : https://prove2.me/theorems/1cad3050-7bd9-4d87-bf08-3b376f531617
-- title:
--   Faithful natural-number enumeration of finite real-valued Borel mark fibres
-- statement:
--   A finite set of real values, such as the range of a finite Borel simple mark, can be enumerated by natural indices below its exact finite cardinality, with every listed value in the original finite set, no repetitions and no omitted values.
-- source:
--   Pinned Mathlib Finset.equivFin at revision 0df444a360eaa60ab8c11dca51a86af692955474, exact-header source inspected. This is the indexing bridge from a SimpleFunc finite real range to the Finset.range (K k) certificate required by 67336b2d.

import Mathlib
open Finset
noncomputable section

theorem AvramDividend.Classical.avram_a21_finite_real_fibre_nat_enumeration_20261112
    (s : Finset ℝ) :
    ∃ u : ℕ → ℝ,
      (∀ i ∈ Finset.range s.card, u i ∈ s) ∧
      (∀ i ∈ Finset.range s.card,
        ∀ j ∈ Finset.range s.card, i ≠ j → u i ≠ u j) ∧
      (∀ y ∈ s, ∃ i ∈ Finset.range s.card, u i = y) := by sorry
