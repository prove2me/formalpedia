-- Prove2me | Theorems.Thm_FasterPrimeEnum_theorem_8_2
-- name    : FasterPrimeEnum.theorem_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:38:42.388594+00:00
-- url     : https://prove2.me/theorems/f8df546e-55a6-4e61-bf0c-4cdbd2b33ae5
-- title:
--   Theorem 8.2 — few intervals of length $U$ hold $g$ square-$y$-rough integers
-- statement:
--   There is an absolute constant $C_0>1$ with the following property. Let $g$, $U$ and $N$ be positive integers with $U\mid N$, and let $y$ be a real number with
--
--   $$
--   \exp\big(C_0g^4\log 5U\,\log(4g^2\log 5U)\big)<y\le N^{1/2}.
--   $$
--
--   Then the number of integers $k\in[0,N/U)$ such that the interval $[kU,(k+1)U)$ contains at least $g$ square-$y$-rough integers is at most
--
--   $$
--   O\Big(\frac NU\Big(\frac{\alpha U}{\log y}\Big)^{g}\Big),\qquad \alpha=6\log(4g^2\log 5U)\prod_{p^2\mid U}\Big(1-\frac1p\Big),
--   $$
--
--   where the product runs over the primes $p$ with $p^2\mid U$ and $\log 5U=\log(5U)$.
--
--   This sieve bound is what makes the exceptional intervals rare, for both the probabilistic and the deterministic algorithm.
--
--   **Formalization Note** $C_0$ and the implied constant are both absolute: they are chosen before $g,U,N,y$. Zero is not square-$y$-rough, which matters for $k=0$.
--
--   Differences from the source:
--   - encoding: O((N/U)(αU/log y)^g) with an absolute implied constant (p.69) → one constant K, chosen with C₀ before g, U, N, y; reason: this is what the O / o(1) notation means for one algorithm (§1.1, p.1); the constants are chosen before every input
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Theorem 8.2, eqs. (8.1)–(8.2), p.68

import Mathlib
import Definitions.Def_FasterPrimeEnum_IsRough

set_option autoImplicit false

namespace FasterPrimeEnum

open Classical in
/-- **Theorem 8.2** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.68.

"There exists an absolute constant C₀ > 1 with the following property. Let g, U and N be positive
integers such that U | N and let y be a real number satisfying
(8.1) exp(C₀g⁴ log 5U log(4g² log 5U)) < y ⩽ N^{1/2}.
Then the number of integers k ∈ [0, N/U) such that there are at least g square-y-rough integers in
the interval [kU, (k + 1)U) is at most O((N/U)(αU/log y)^g) where
(8.2) α := 6 log(4g² log 5U) ∏_{p²|U} (1 − 1/p)."

**Formalization Note.** `log 5U` is `log(5U)`, natural. The product runs over the primes `p` with
`p² | U`. `C₀` and the implied constant `K` are absolute: both are chosen before `g, U, N, y` (p.69:
the implied constants of §8 are absolute). Zero is not square-rough (Remark 8.5), so `k = 0` is
counted correctly. -/
theorem theorem_8_2 :
    ∃ C₀ : ℝ, 1 < C₀ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ g U N : ℕ, 0 < g → 0 < U → 0 < N → U ∣ N → ∀ y : ℝ,
        Real.exp (C₀ * (g : ℝ) ^ 4 * Real.log (5 * U) *
            Real.log (4 * (g : ℝ) ^ 2 * Real.log (5 * U))) < y →
        y ≤ Real.sqrt N →
        ((((Finset.range (N / U)).filter fun k =>
            g ≤ ((Finset.Ico (k * U) ((k + 1) * U)).filter fun n => IsSquareRough y n).card).card
            : ℕ) : ℝ) ≤
          K * ((N : ℝ) / U) *
            (6 * Real.log (4 * (g : ℝ) ^ 2 * Real.log (5 * U)) *
                (∏ p ∈ U.primeFactors.filter (fun p => p ^ 2 ∣ U), (1 - 1 / (p : ℝ))) *
                U / Real.log y) ^ g := by sorry

end FasterPrimeEnum
