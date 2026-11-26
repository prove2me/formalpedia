-- Prove2me | Theorems.Thm_Erdos287_chen_switching_triples_from_rough_factor_set
-- name    : Erdos287.chen_switching_triples_from_rough_factor_set
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:18:32.379934+00:00
-- url     : https://prove2.me/theorems/924ec7e1-390d-5545-8c15-732932b0a79a
-- title:
--   Chen switching triples from a rough factor set
-- statement:
--   Let $n$ be a positive integer whose prime divisors all exceed $Y$. Suppose every prime divisor of $n$ in $(Y,Z]$ has exponent one, and let $S$ be the set of those primes. Let $T$ count triples $p<q<r$ in $S$ such that $n=pqrs$ for an integer $s$ whose prime divisors are at least $q$. Then $2\mathbf 1_{S=\varnothing}+|S|\le 2+T$.
-- source:
--   Jori Merikoski, Limit points of normalized prime gaps, Lemma 13, https://arxiv.org/abs/1811.03008. Switching transfer for Erdős Problem 287.

import Mathlib

theorem Erdos287.chen_switching_triples_from_rough_factor_set (n Y Z : ℕ) (hn : 0 < n)
    (hrough : ∀ l : ℕ, l.Prime → l ∣ n → Y < l)
    (hsquare : ∀ l : ℕ, l.Prime → Y < l → l ≤ Z → ¬ l ^ 2 ∣ n) :
    let S := n.primeFactors.filter (fun l => Y < l ∧ l ≤ Z)
    let triples := (Finset.product (Finset.product S S) S).filter (fun t => t.1.1 < t.1.2 ∧ t.1.2 < t.2 ∧
      ∃ s ∈ Finset.range (n + 1), n = t.1.1 * t.1.2 * t.2 * s ∧
        ∀ l ∈ s.primeFactors, t.1.2 ≤ l)
    2 * (if S.card = 0 then 1 else 0) + S.card ≤ 2 + triples.card := by sorry
