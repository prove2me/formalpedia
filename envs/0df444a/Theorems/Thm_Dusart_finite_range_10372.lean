-- Prove2me | Theorems.Thm_Dusart_finite_range_10372
-- name    : Dusart.finite_range_10372
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:35:07.824973+00:00
-- url     : https://prove2.me/theorems/afb22cde-adb1-4307-9ed9-db8634f3b1ef
-- title:
--   Dusart's bound for $\sum_{p\le x}1/p$ on $[10372,3594641]$
-- statement:
--   For every real $x$ with $10372\le x\le 3594641$,
--
--   $$\sum_{p\le x}\frac1p-\log\log x-B\le\frac{1}{10\log^2x}+\frac{4}{15\log^3x},\qquad B=\gamma+\sum_p\Big(\log\Big(1-\frac1p\Big)+\frac1p\Big),$$
--
--   where $p$ runs over primes and $\gamma$ is Euler's constant. This is the finite range of Dusart's Theorem 6.10, which Dusart closes by a computer check; here it is a kernel-checked certificate.
--
--   **Formalization Note** $B$ is written with Mathlib's `tsum` over `Nat.Primes`; the sum over $p\le x$ is over primes in `Finset.range (⌊x⌋₊ + 1)`.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 6.10 (upper bound for x ≥ 10372) and Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); the proof of Theorem 6.10 closes the range below 3 594 641 by a computer check.

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.SumPrimeReciprocals

theorem Dusart.finite_range_10372 (x : ℝ) (h1 : 10372 ≤ x) (h2 : x ≤ 3594641) :
    (∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), (1 : ℝ) / p) - Real.log (Real.log x) -
        (Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      1 / (10 * Real.log x ^ 2) + 4 / (15 * Real.log x ^ 3) := by sorry
