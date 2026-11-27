-- Prove2me | Theorems.Thm_Erdos287_cardinality_reducing_reciprocal_edit_blocked
-- name    : Erdos287.cardinality_reducing_reciprocal_edit_blocked
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-27T00:01:53.719578+00:00
-- url     : https://prove2.me/theorems/0739337f-0764-47f8-9841-db50f353e8c5
-- title:
--   An exact cardinality-reducing edit must leave an uncovered adjacent pair
-- statement:
--   For a minimum-cardinality exact pair cover, an edit can remove a set of selected denominators and insert a smaller disjoint set of missing denominators with equal reciprocal sum. When the edit preserves the left endpoint, some adjacent pair consists either of two removed terms or of a removed term and an old omission that the edit fails to fill.
-- source:
--   Erdős Problem 287. Simultaneous reciprocal edits of cardinality-minimal covers.

import Mathlib

theorem Erdos287.cardinality_reducing_reciprocal_edit_blocked (D R A : Finset ℕ) (m M : ℕ)
    (hm : m ∈ D) (hD : D ⊆ Finset.Icc m M)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hmin : ∀ E : Finset ℕ, m ∈ E → E ⊆ Finset.Icc m M →
      (∀ x, m ≤ x → x + 1 ≤ M → x ∈ E ∨ x + 1 ∈ E) →
      (∑ n ∈ E, (1 : ℚ) / n = 1) → D.card ≤ E.card)
    (hR : R ⊆ D) (hmR : m ∉ R) (hA : A ⊆ Finset.Icc m M) (hAD : Disjoint A D)
    (hexact : ∑ n ∈ A, (1 : ℚ) / n = ∑ n ∈ R, (1 : ℚ) / n)
    (hsize : A.card < R.card) :
    ∃ x, m ≤ x ∧ x + 1 ≤ M ∧
      ((x ∈ R ∧ x + 1 ∈ R) ∨
        (x ∈ R ∧ x + 1 ∉ D ∧ x + 1 ∉ A) ∨
        (x + 1 ∈ R ∧ x ∉ D ∧ x ∉ A)) := by sorry
