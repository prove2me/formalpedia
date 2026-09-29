-- Prove2me | Theorems.Thm_DivisorSums_sum_sqrt_gcd_div_le_log_two_mul
-- name    : DivisorSums.sum_sqrt_gcd_div_le_log_two_mul
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T16:13:24.098198+00:00
-- url     : https://prove2.me/theorems/d438223d-f5b8-4c12-bc13-1a9941a7f8d0
-- title:
--   A bound for a weighted $\sqrt{\gcd}$ divisor sum
-- statement:
--   **A harmonic sum weighted by $\sqrt{\gcd(n,s)}$.**
--
--   For every $n \ge 1$,
--
--   $$\sum_{s=1}^{n} \frac{\sqrt{\gcd(n,s)}}{s}
--   \;\le\; \frac{d(n)\,\log(2n)}{\log 2},$$
--
--   where $d(n)$ is the number of divisors of $n$.
--
--   Without the $\sqrt{\gcd}$ weight the sum is the harmonic sum $\log n + O(1)$. The weight can be
--   as large as $\sqrt n$ (at $s = n$), so a trivial bound would lose a factor of $\sqrt n$; the
--   theorem says the true cost is only a factor $d(n)$, which is $n^{o(1)}$.
--
--   The mechanism is to sort $s$ by $g = \gcd(n,s)$: for each divisor $g \mid n$ the terms with
--   $\gcd(n,s) = g$ contribute at most $\sqrt g \sum_{m \le n/g} \tfrac{1}{gm} \le
--   \tfrac{\log(2n)}{\sqrt g}\cdot\tfrac{1}{\sqrt g}\cdot\sqrt g$, and summing over the $d(n)$
--   divisors gives the stated bound. The constant $(\log 2)^{-1}$ and the shift to $\log(2n)$ come
--   from bounding the inner harmonic sums dyadically, which also keeps the estimate valid at
--   $n = 1$.
--
--   Weighted sums of this shape occur when estimating Kloosterman-type sums and in sieve
--   manipulations, where a gcd weight appears after grouping residues by their common factor with
--   the modulus.
--
--   **Formalization note.** `n.divisors.card` is $d(n)$; the sum runs over $s \in [1,n]$ and all
--   quantities are real.
-- source:
--   Elementary divisor-sum estimate of the kind used in Kloosterman-sum and sieve arguments; cf. Iwaniec & Kowalski, *Analytic Number Theory*, §1.4. Lean proof extracted from `Salt/Weil/GcdDivisorSum.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace DivisorSums

theorem sum_sqrt_gcd_div_le_log_two_mul (n : ℕ) (hn : n ≠ 0) :
    ∑ s ∈ Finset.Icc 1 n, Real.sqrt (Nat.gcd n s : ℝ) / s
      ≤ (Real.log 2)⁻¹ * (n.divisors.card : ℝ) * Real.log (2 * n) := by sorry

end DivisorSums
