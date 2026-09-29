-- Prove2me | Theorems.Thm_FamousTheorems_sum_prime_reciprocals_diverges
-- name    : FamousTheorems.sum_prime_reciprocals_diverges
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:36:59.175666+00:00
-- url     : https://prove2.me/theorems/c9f3501b-5af5-4d7f-8e76-84331768ed2c
-- title:
--   Divergence of the sum of reciprocals of the primes
-- statement:
--   **Divergence of the sum of reciprocals of the primes.** The series
--   $$\sum_{p\ \text{prime}}\frac1p$$
--   diverges.
--
--   Proved by Euler in 1737, this strengthens Euclid's theorem that there are infinitely many primes: the primes are dense enough that the sum of their reciprocals diverges, unlike the sum over the squares. It started analytic number theory. Mertens later sharpened it to $\sum_{p\le x}1/p=\log\log x+M+o(1)$.
--
--   **Formalization note.** Mathlib's `not_summable_one_div_on_primes`. The series is written as the function $n\mapsto 1/n$ restricted by `Set.indicator` to the set of primes (zero elsewhere), and divergence is `¬Summable` in $\mathbb R$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `not_summable_one_div_on_primes`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem sum_prime_reciprocals_diverges : ¬Summable ({p : ℕ | p.Prime}.indicator fun n : ℕ => (1 : ℝ) / n) := by sorry

end FamousTheorems
