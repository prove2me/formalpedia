-- Prove2me | Theorems.Thm_ChebyshevBounds_primes_in_interval_ge
-- name    : ChebyshevBounds.primes_in_interval_ge
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T12:17:02.278546+00:00
-- url     : https://prove2.me/theorems/7a8c60aa-4818-479e-968e-2c9eda87b63b
-- title:
--   Chebyshev lower bound for primes in a long interval
-- statement:
--   **A Chebyshev-type lower bound for the number of primes in a long interval.**
--
--   There are constants $c > 0$ and $N_0$ such that for all $N \ge N_0$,
--
--   $$\pi(64N) - \pi(N) \;\ge\; c\,\frac{N}{\log N},$$
--
--   where $\pi$ is the prime counting function.
--
--   In words: the interval $(N, 64N]$ contains at least a constant multiple of $N/\log N$ primes —
--   the order of magnitude predicted by the prime number theorem, obtained by elementary means.
--   The prime number theorem would give the sharper asymptotic $\pi(64N) - \pi(N) \sim 63N/\log N$,
--   but that is not needed here, and the elementary route gives an effective $N_0$.
--
--   The dilation factor $64$ is not essential to the phenomenon — any fixed factor $>1$ admits such
--   a bound, by Bertrand-type arguments — but a concrete large factor makes the elementary
--   Chebyshev estimates comfortable, since the error terms in
--   $\theta(x) \asymp x$ need room to be absorbed.
--
--   Results of this shape are the standard input wherever one needs "enough primes in a dyadic-type
--   range" without invoking the prime number theorem: sieve setups, constructions of admissible
--   tuples in the small-gaps circle of ideas, and counting arguments where only the order of
--   magnitude matters.
--
--   **Formalization note.** `Nat.primeCounting N` is $\pi(N)$; both counts are cast to $\mathbb{R}$
--   so the difference and the bound live in $\mathbb{R}$. The constants $c$ and $N_0$ are
--   existentially quantified rather than named.
-- source:
--   Classical Chebyshev-type estimate; see Montgomery & Vaughan, *Multiplicative Number Theory I*, §2.1-2.2, and Nathanson, *Elementary Methods in Number Theory*, Ch. 8. Lean proof extracted from `Salt/Maynard/ChebyshevInterval.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace ChebyshevBounds

theorem primes_in_interval_ge :
    ∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧ ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) / Real.log N ≤
        ((Nat.primeCounting (64 * N) : ℝ) - (Nat.primeCounting N : ℝ)) := by sorry

end ChebyshevBounds
