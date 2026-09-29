-- Prove2me | Theorems.Thm_DivisorSums_sum_mul_subst
-- name    : DivisorSums.sum_mul_subst
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:12:15.450384+00:00
-- url     : https://prove2.me/theorems/b7a9a3c5-47b5-41ac-bcd3-a294ad239879
-- title:
--   Reindexing a divisor sum supported on multiples of $k$
-- statement:
--   **A divisor sum supported on multiples of $k$ can be reindexed by the cofactor.**
--
--   Let $f$ vanish at every divisor of $n$ that is *not* a multiple of $k$. Then
--
--   $$\sum_{l \mid n} f(l) \;=\; \sum_{m \mid n} \begin{cases} f(km) & \text{if } km \mid n,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   By hypothesis only the divisors $l$ with $k \mid l$ contribute on the left, and each such $l$
--   is uniquely $l = km$ with $m = l/k$; moreover $l \mid n$ forces $m \mid n$, so the substitution
--   $l \leftrightarrow km$ is a bijection between $\{l \mid n : k \mid l\}$ and
--   $\{m \mid n : km \mid n\}$. The guard `if k * m \u2223 n` on the right is what discards the values
--   of $m$ that do not arise this way, making the two sums equal term for term.
--
--   This reindexing is used constantly in sieve theory, where sums over squarefree $l$ supported on
--   the sifting primes are repeatedly rewritten in terms of a fixed factor $k$ and a varying
--   cofactor — in Selberg's sieve, for instance, when the quadratic form in the $\lambda_d$ is
--   diagonalised.
--
--   **Formalization note.** `n.divisors` excludes $0$ and is empty when $n = 0$, so no
--   degenerate case arises; the hypothesis is only imposed at divisors of $n$, which is all the
--   sum sees.
-- source:
--   Standard in sieve theory; see Halberstam & Richert, *Sieve Methods*, Ch. 3. Lean proof extracted from `Salt/Brun/SelbergPort.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace DivisorSums

theorem sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬k ∣ l → f l = 0) :
    ∑ l ∈ n.divisors, f l = ∑ m ∈ n.divisors, if k * m ∣ n then f (k * m) else 0 := by sorry

end DivisorSums
