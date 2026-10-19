-- Prove2me | Theorems.Thm_Dusart_reciprocal_primes_of_chebyshev
-- name    : Dusart.reciprocal_primes_of_chebyshev
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:35:04.44918+00:00
-- url     : https://prove2.me/theorems/80f743a0-d076-44fe-97e7-d8c1c4ae5f43
-- title:
--   Dusart's bound for $\sum_{p\le x}1/p$ from the explicit Chebyshev estimate
-- statement:
--   Assume Dusart's explicit Chebyshev estimate (Theorem 5.2 with $k=2$, $\eta=0.2$):
--
--   $$|\theta(t)-t|\le\frac{t}{5\log^2t}\qquad(t\ge 3594641),$$
--
--   where $\theta(t)=\sum_{p\le t}\log p$. Then for every real $x\ge10372$,
--
--   $$\sum_{p\le x}\frac1p-\log\log x-B\le\frac{1}{10\log^2x}+\frac{4}{15\log^3x},\qquad B=\gamma+\sum_p\Big(\log\Big(1-\frac1p\Big)+\frac1p\Big).$$
--
--   This is Dusart's Theorem 6.10 (upper bound) with its only analytic input made explicit. The deduction combines partial summation, the identification of the limit of $\sum_{p\le x}1/p-\log\log x$ with Mertens' constant $B$, and the finite range $[10372,3594641]$.
--
--   **Formalization Note** $\theta$ is Mathlib's `Chebyshev.theta`; $B$ is written with `tsum` over `Nat.Primes`.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 6.10 (upper bound for x ≥ 10372) and Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); the proof of Theorem 6.10 closes the range below 3 594 641 by a computer check.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

theorem Dusart.reciprocal_primes_of_chebyshev
    (hθ : ∀ t : ℝ, 3594641 ≤ t → |Chebyshev.theta t - t| ≤ (1 / 5) * t / Real.log t ^ 2)
    (x : ℝ) (hx : 10372 ≤ x) :
    (∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), (1 : ℝ) / p) - Real.log (Real.log x) -
        (Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      1 / (10 * Real.log x ^ 2) + 4 / (15 * Real.log x ^ 3) := by sorry
