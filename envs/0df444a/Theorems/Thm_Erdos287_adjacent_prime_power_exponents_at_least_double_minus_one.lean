-- Prove2me | Theorems.Thm_Erdos287_adjacent_prime_power_exponents_at_least_double_minus_one
-- name    : Erdos287.adjacent_prime_power_exponents_at_least_double_minus_one
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T06:05:35.474655+00:00
-- url     : https://prove2.me/theorems/b20e3ca5-ad9a-4e7c-af08-8906baac2954
-- title:
--   Exponent separation for repeated adjacency of prime-power multiples
-- statement:
--   Let $p\ne q$ be primes, $c,d$ positive integers, and $a,b,h,j$ nonnegative integers with $h>0$. If $cp^a$ and $dq^b$ are adjacent and $cp^{a+h}$ and $dq^{b+j}$ are adjacent, then $a\le h+1$. Consequently, for fixed cofactors and primes, the first-prime exponents of repeated adjacent pairs grow at least geometrically once the first exponent exceeds one.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Exponent separation bounds the frequency of adjacency in fixed-prime high valuation supports.

import Mathlib

theorem Erdos287.adjacent_prime_power_exponents_at_least_double_minus_one (p q c d a b h j : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hc : 0 < c) (hd : 0 < d) (hh : 0 < h)
    (h₁ : |(c : ℤ) * (p : ℤ) ^ a - (d : ℤ) * (q : ℤ) ^ b| = 1)
    (h₂ : |(c : ℤ) * (p : ℤ) ^ (a + h) - (d : ℤ) * (q : ℤ) ^ (b + j)| = 1) :
    a ≤ h + 1 := by sorry
