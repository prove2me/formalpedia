-- Prove2me | Theorems.Thm_DivisorSums_sum_sqrt_gcd_dyadic_le_of_dvd
-- name    : DivisorSums.sum_sqrt_gcd_dyadic_le_of_dvd
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T16:26:28.476361+00:00
-- url     : https://prove2.me/theorems/9130a443-0581-40a4-a9a1-455f86918fc3
-- title:
--   A dyadic bound for $\sum \sqrt{\gcd}$ over a divisor
-- statement:
--   **A dyadic block sum of $\sqrt{\gcd(k_0,m)}$.**
--
--   Let $k_0 \mid k$ with $k \ne 0$. Then over any dyadic block,
--
--   $$\sum_{M < m \le 2M} \sqrt{\gcd(k_0,m)} \;\le\; 2M\,d(k),$$
--
--   where $d(k)$ is the number of divisors of $k$.
--
--   The block has $M$ terms, and the weight $\sqrt{\gcd(k_0,m)}$ can be as large as $\sqrt{k_0}$,
--   so the trivial bound is $M\sqrt{k_0}$. The content is that the true size is $M \cdot k^{o(1)}$:
--   sorting $m$ by $g = \gcd(k_0,m)$, the number of $m$ in the block divisible by $g$ is at most
--   $2M/g$, so each divisor $g$ contributes at most $\sqrt g \cdot 2M/g = 2M/\sqrt g \le 2M$, and
--   there are at most $d(k_0) \le d(k)$ divisors to consider.
--
--   Dyadic blocks are the natural unit here because the count $2M/g$ is only useful when the block
--   length is comparable to its endpoints; summing such blocks recovers bounds over full ranges
--   with an extra logarithmic factor. Estimates of exactly this shape arise when bounding
--   Kloosterman sums and in the large-sieve treatment of gcd-weighted averages.
--
--   **Formalization note.** `k.divisors.card` is $d(k)$, and the hypothesis $k_0 \mid k$ lets the
--   divisor count of the larger modulus $k$ dominate that of $k_0$.
-- source:
--   Elementary divisor-sum estimate of the kind used in Kloosterman-sum bounds; cf. Iwaniec & Kowalski, *Analytic Number Theory*, §1.4. Lean proof extracted from `Salt/Weil/GcdDivisorSum.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace DivisorSums

theorem sum_sqrt_gcd_dyadic_le_of_dvd {k₀ k M : ℕ} (hk : k ≠ 0) (hdvd : k₀ ∣ k) :
    ∑ m ∈ Finset.Ioc M (2 * M), Real.sqrt (Nat.gcd k₀ m : ℝ)
      ≤ 2 * M * (k.divisors.card : ℝ) := by sorry

end DivisorSums
