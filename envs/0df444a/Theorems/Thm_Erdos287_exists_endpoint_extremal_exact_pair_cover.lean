-- Prove2me | Theorems.Thm_Erdos287_exists_endpoint_extremal_exact_pair_cover
-- name    : Erdos287.exists_endpoint_extremal_exact_pair_cover
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-27T00:20:27.318673+00:00
-- url     : https://prove2.me/theorems/c75cd58a-2b5f-4af2-917d-95b6ae3197c2
-- title:
--   Extremal endpoints for an exact pair cover
-- statement:
--   If a set of denominators above one sums reciprocally to one and covers every adjacent pair between its endpoints, there is such a set that first minimizes the maximum, then maximizes the minimum, then minimizes cardinality for those endpoints.
-- source:
--   Erdős Problem 287. Exact reciprocal covers with extremal endpoints.

import Mathlib

theorem Erdos287.exists_endpoint_extremal_exact_pair_cover (D : Finset ℕ) (m M : ℕ) (hm : 1 < m)
    (hmD : m ∈ D) (hMD : M ∈ D) (hD : D ⊆ Finset.Icc m M)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1) :
    ∃ (l u : ℕ) (E : Finset ℕ), u ≤ M ∧ 1 < l ∧ l ∈ E ∧ u ∈ E ∧
      E ⊆ Finset.Icc l u ∧
      (∀ x, l ≤ x → x + 1 ≤ u → x ∈ E ∨ x + 1 ∈ E) ∧
      (∑ n ∈ E, (1 : ℚ) / n = 1) ∧
      (∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
        F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
        (∑ n ∈ F, (1 : ℚ) / n = 1) →
        u ≤ b ∧ (b = u → a ≤ l) ∧ (b = u → a = l → E.card ≤ F.card)) := by sorry
