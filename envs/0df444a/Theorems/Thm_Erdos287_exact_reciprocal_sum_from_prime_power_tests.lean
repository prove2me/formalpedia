-- Prove2me | Theorems.Thm_Erdos287_exact_reciprocal_sum_from_prime_power_tests
-- name    : Erdos287.exact_reciprocal_sum_from_prime_power_tests
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T06:06:21.569308+00:00
-- url     : https://prove2.me/theorems/8785f63d-1252-538b-b4bb-24ee5ea41f1d
-- title:
--   Prime-power congruences characterize an exact reciprocal sum in a short interval
-- statement:
--   Let $D$ be a finite set of positive denominators, $C$ a positive common multiple, and $s=\sum_{n\in D}1/n$. Take distinct primes $p\in P$ and exponents $e_p$ with $p^{e_p}\mid C$, and let $A=\prod_{p\in P}p^{e_p}$. Assume $W>0$, $C/A\le W$, and $1\le s<1+1/W$. Then $s=1$ if and only if for each $p\in P$,
--
--   $$p^{e_p}\mid\sum_{\substack{n\in D\\ p^{e_p}\nmid C/n}} C/n.$$
--
--   In particular, using all prime powers in the factorization of $C$ gives an exact criterion for reciprocal sums in $[1,2)$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Completeness of local prime-power congruences under a certified reciprocal mass interval.

import Mathlib

theorem Erdos287.exact_reciprocal_sum_from_prime_power_tests (D : Finset ℕ) (C W : ℕ) (hC : 0 < C)
    (hpos : ∀ n ∈ D, 0 < n) (hdiv : ∀ n ∈ D, n ∣ C)
    (P : Finset ℕ) (e : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hpow : ∀ p ∈ P, p ^ e p ∣ C)
    (hwidth : C / (∏ p ∈ P, p ^ e p) ≤ W)
    (hlo : (1 : ℚ) ≤ ∑ n ∈ D, (1 : ℚ) / n)
    (hhi : (∑ n ∈ D, (1 : ℚ) / n) < 1 + (1 : ℚ) / W) :
    (∑ n ∈ D, (1 : ℚ) / n) = 1 ↔
      ∀ p ∈ P, p ^ e p ∣ ∑ n ∈ D.filter (fun n => ¬ p ^ e p ∣ C / n), C / n := by sorry
