-- Prove2me | Theorems.Thm_Erdos287_exists_minimum_cardinality_exact_pair_cover
-- name    : Erdos287.exists_minimum_cardinality_exact_pair_cover
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T23:48:26.835814+00:00
-- url     : https://prove2.me/theorems/0d9e0880-6bc9-50fc-aa5c-38682107bf5b
-- title:
--   A minimum-cardinality exact pair cover of a counterexample interval
-- statement:
--   If $1< f(0)<\cdots<f(k-1)$ have reciprocal sum one and all consecutive gaps at most two, there is a subset of their denominator interval that retains the left endpoint, has reciprocal sum one, covers every adjacent pair, and has minimum cardinality among all subsets with these properties.
-- source:
--   Erdős Problem 287. Choosing a canonical cardinality-minimal exact cover.

import Mathlib

theorem Erdos287.exists_minimum_cardinality_exact_pair_cover (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2) :
    let m := f 0
    let M := f (k - 1)
    ∃ D : Finset ℕ, D.card ≤ k ∧ 1 < m ∧ m ∈ D ∧ D ⊆ Finset.Icc m M ∧
      (∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D) ∧
      (∑ n ∈ D, (1 : ℚ) / n = 1) ∧
      (∀ E : Finset ℕ, m ∈ E → E ⊆ Finset.Icc m M →
        (∀ x, m ≤ x → x + 1 ≤ M → x ∈ E ∨ x + 1 ∈ E) →
        (∑ n ∈ E, (1 : ℚ) / n = 1) → D.card ≤ E.card) := by sorry
