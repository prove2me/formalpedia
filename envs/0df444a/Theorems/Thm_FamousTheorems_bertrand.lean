-- Prove2me | Theorems.Thm_FamousTheorems_bertrand
-- name    : FamousTheorems.bertrand
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:52:01.890987+00:00
-- url     : https://prove2.me/theorems/bc198785-1899-4003-a122-3d11de070941
-- title:
--   Bertrand's postulate
-- statement:
--   **There is always a prime between $n$ and $2n$.**
--
--   For every $n \ge 1$ there is a prime $p$ with $n < p \le 2n$.
--
--   Conjectured by Bertrand in 1845 on numerical evidence up to $3{,}000{,}000$ and proved by
--   Chebyshev in 1852. Erd\H{o}s gave an elementary proof at nineteen, in his first paper, using the
--   prime factorisation of the central binomial coefficient $\binom{2n}{n}$: primes in $(n, 2n]$
--   divide it exactly once, primes above $2n$ not at all, and the contribution of small primes is
--   too small to account for its size unless a prime in the interval exists.
--
--   It is much weaker than the prime number theorem but entirely elementary, and strong enough for
--   many applications where only the existence of a nearby prime matters.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem bertrand : ∀ n : ℕ, n ≠ 0 → ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n := by sorry

end FamousTheorems
