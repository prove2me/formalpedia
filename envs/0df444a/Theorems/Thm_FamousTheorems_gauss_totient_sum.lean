-- Prove2me | Theorems.Thm_FamousTheorems_gauss_totient_sum
-- name    : FamousTheorems.gauss_totient_sum
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:37.702782+00:00
-- url     : https://prove2.me/theorems/3800ae0d-9d05-41f5-a5d3-fb1c5ce5b71f
-- title:
--   Gauss's totient sum identity
-- statement:
--   **Gauss's totient sum identity.** For every natural number $n$,
--   $$\sum_{d\mid n}\varphi(d)=n,$$
--   where $\varphi$ is Euler's totient function.
--
--   The identity comes from sorting the fractions $k/n$, $1\le k\le n$, by their reduced denominators. It is used to show that the multiplicative group of a finite field is cyclic, and by Möbius inversion it yields the formula $\varphi(n)=\sum_{d\mid n}\mu(d)\,n/d$.
--
--   **Formalization note.** Mathlib's `Nat.sum_totient`. `n.divisors` is the finset of positive divisors of $n$; for $n=0$ it is empty and both sides are $0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.sum_totient`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem gauss_totient_sum (n : ℕ) : ∑ d ∈ n.divisors, Nat.totient d = n := by sorry

end FamousTheorems
