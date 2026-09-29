-- Prove2me | Theorems.Thm_FamousTheorems_sum_range_pow
-- name    : FamousTheorems.sum_range_pow
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:42:17.78737+00:00
-- url     : https://prove2.me/theorems/7e3a9469-8c5d-4e8b-9ed2-f1fcbfea57bf
-- title:
--   Sum of the kth powers (Faulhaber's formula)
-- statement:
--   **Faulhaber's formula** for sums of powers.
--
--   For all $n, p$,
--   $$\sum_{k=0}^{n-1} k^p \;=\; \frac{1}{p+1}\sum_{i=0}^{p} \binom{p+1}{i} B_i\, n^{\,p+1-i},$$
--   where $B_i$ are the Bernoulli numbers.
--
--   So $\sum_{k<n} k^p$ is always a polynomial in $n$ of degree $p+1$ with leading coefficient
--   $\tfrac{1}{p+1}$, and the formula names every coefficient at once. For $p = 1$ it returns
--   $n(n-1)/2$; for $p = 2$, $n(n-1)(2n-1)/6$. Before Faulhaber each case was found separately; the
--   Bernoulli numbers are precisely the universal constants that make one formula cover all $p$.
--
--   Faulhaber computed the cases up to $p = 17$ in 1631. Jacob Bernoulli found the general pattern and
--   introduced the numbers now named after him in *Ars Conjectandi* (posthumous, 1713) — he remarked
--   that with it he summed the tenth powers of the first thousand integers "in half a quarter of an hour".
--   The same numbers reappear in the Euler–Maclaurin formula and in the values $\zeta(2k)$.
--
--   **Formalization note.** The sum runs over `Finset.range n`, i.e. $k = 0, \dots, n-1$, and everything is
--   over $\mathbb{Q}$ so that the division is exact. `bernoulli` is the convention with $B_1 = +1/2$. The
--   result is Mathlib's `sum_range_pow`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem sum_range_pow (n p : ℕ) :
    (∑ k ∈ Finset.range n, (k : ℚ) ^ p) =
      ∑ i ∈ Finset.range (p + 1),
        bernoulli i * ((p + 1).choose i) * (n : ℚ) ^ (p + 1 - i) / (p + 1) := by sorry

end FamousTheorems
