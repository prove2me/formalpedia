-- Prove2me | Theorems.Thm_Erdos287_endpoint_extremal_cover_trimmed_mass_obstruction
-- name    : Erdos287.endpoint_extremal_cover_trimmed_mass_obstruction
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-27T00:22:05.860966+00:00
-- url     : https://prove2.me/theorems/3b5eaffa-ff40-4552-8ff8-eca6de3b7d8b
-- title:
--   A proper subinterval cannot refill the reciprocal mass of the discarded endpoints
-- statement:
--   In an exact pair cover of minimum possible maximum and then maximum possible minimum, choose a proper subinterval. The reciprocal sum of the deleted selected denominators cannot equal the sum of any set of old omissions in that subinterval.
-- source:
--   Erdős Problem 287. Exact reciprocal covers with extremal endpoints.

import Mathlib

theorem Erdos287.endpoint_extremal_cover_trimmed_mass_obstruction (D A : Finset ℕ) (m M l u : ℕ) (hm : 1 < m)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hextreme : ∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
      F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
      (∑ n ∈ F, (1 : ℚ) / n = 1) → M ≤ b ∧ (b = M → a ≤ m))
    (hml : m ≤ l) (huM : u ≤ M) (htrim : m < l ∨ u < M)
    (hA : A ⊆ Finset.Icc l u) (hAD : Disjoint A D) :
    (∑ n ∈ A, (1 : ℚ) / n) ≠
      ∑ n ∈ D.filter (fun n => n < l ∨ u < n), (1 : ℚ) / n := by sorry
