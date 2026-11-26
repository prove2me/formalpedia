-- Prove2me | Theorems.Thm_Erdos287_large_prime_adjacency_edge_unique
-- name    : Erdos287.large_prime_adjacency_edge_unique
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:46:26.22592+00:00
-- url     : https://prove2.me/theorems/d6a14fba-3a1f-5608-b2e7-cf6cdcdc36e0
-- title:
--   A pair of large prime layers has at most one adjacency
-- statement:
--   Let $p,q$ be distinct primes with $pq\ge2M$. There is at most one start $x$ with $x+1\le M$ such that one of $x,x+1$ is a multiple of $p$ and the other is a multiple of $q$. Both orientations are allowed.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.large_prime_adjacency_edge_unique (p q M x y : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hproduct : 2 * M ≤ p * q) (hx : x + 1 ≤ M) (hy : y + 1 ≤ M)
    (hleft : (p ∣ x ∧ q ∣ x + 1) ∨ (q ∣ x ∧ p ∣ x + 1))
    (hright : (p ∣ y ∧ q ∣ y + 1) ∨ (q ∣ y ∧ p ∣ y + 1)) :
    x = y := by sorry
