-- Prove2me | Theorems.Thm_FCP_Mills_prime_between_consecutive_cubes
-- name    : FCP.Mills.prime_between_consecutive_cubes
-- status  : Open
-- author  : @Himan
-- created : 2026-11-15T04:20:00.656898+00:00
-- url     : https://prove2.me/theorems/8804069e-dd83-48ee-806f-74685779d388
-- title:
--   A prime strictly between consecutive large cubes: $N^3 < p < (N+1)^3 - 1$
-- statement:
--   Let $p_n$ denote the $n$-th prime. Ingham (1937) proved that there is a constant $K$ with $p_{n+1} - p_n < K\,p_n^{5/8}$ for all $n$. Mills (1947) drew from this the following lemma, which is the only arithmetic input of his prime-representing function: there is a threshold $N_0$ such that for every integer $N \ge N_0$ some prime $p$ satisfies
--
--   $$N^3 < p < (N+1)^3 - 1.$$
--
--   Indeed, if $p_n$ is the largest prime not exceeding $N^3$, then $N^3 < p_{n+1} < N^3 + K N^{15/8}$, and $K N^{15/8} < 3N^2 + 3N$ once $N > K^8$.
--
--   The statement is a theorem, and the threshold is what makes it one: whether a prime lies between every pair of consecutive cubes is not known unconditionally. It is the single open child of the reduction of Mills' theorem, where it supplies each step $P_{k+1} \in (P_k^3, (P_k+1)^3 - 1)$ of Mills' sequence of primes.
--
--   **Formalization Note** The upper bound $p < (N+1)^3 - 1$ is written as $p + 1 < (N+1)^3$ so that no truncated subtraction of natural numbers appears. All quantities are natural numbers.
-- source:
--   W. H. Mills, A prime-representing function, Bull. Amer. Math. Soc. 53 (1947), 604, the Lemma; it rests on A. E. Ingham, On the difference between consecutive primes, Quart. J. Math. Oxford Ser. 8 (1937), 255-266.

import Mathlib
import Definitions.Def_FCP_Mills

namespace FCP.Mills

theorem prime_between_consecutive_cubes :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ p : ℕ, p.Prime ∧ N ^ 3 < p ∧ p + 1 < (N + 1) ^ 3 := by sorry

end FCP.Mills
