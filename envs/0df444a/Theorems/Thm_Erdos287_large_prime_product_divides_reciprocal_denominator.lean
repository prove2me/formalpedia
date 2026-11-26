-- Prove2me | Theorems.Thm_Erdos287_large_prime_product_divides_reciprocal_denominator
-- name    : Erdos287.large_prime_product_divides_reciprocal_denominator
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T06:15:49.379171+00:00
-- url     : https://prove2.me/theorems/e52d7101-64fb-577f-8d16-6f27eb821689
-- title:
--   The product of retained large primes divides the reduced reciprocal denominator
-- statement:
--   Let $D\subseteq\{1,\ldots,M\}$ be a finite set of denominators and $P$ a finite set of primes. For every $p\in P$, set $B_p=\lfloor M/p\rfloor$ and suppose $B_p\,\mathrm{lcm}(1,\ldots,B_p)<p$. Suppose also that $D$ contains a multiple of every $p\in P$. Then the product of the primes in $P$ divides the reduced denominator of $\sum_{n\in D}1/n$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Accumulation of the large primes in the exact reduced reciprocal denominator.

import Mathlib

theorem Erdos287.large_prime_product_divides_reciprocal_denominator (D P : Finset ℕ) (M : ℕ)
    (hD : ∀ n ∈ D, 0 < n ∧ n ≤ M)
    (hP : ∀ p ∈ P, p.Prime)
    (hsmall : ∀ p ∈ P, (M / p) * Nat.lcmUpto (M / p) < p)
    (hmem : ∀ p ∈ P, ∃ n ∈ D, p ∣ n) :
    (∏ p ∈ P, p) ∣ (∑ n ∈ D, (1 : ℚ) / n).den := by sorry
