-- Prove2me | Theorems.Thm_DivisorBounds_card_divisors_pow_le
-- name    : DivisorBounds.card_divisors_pow_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:26:05.824977+00:00
-- url     : https://prove2.me/theorems/10526832-af12-4685-9c4d-d0ce42872c68
-- title:
--   A power of the divisor function is sub-linear
-- statement:
--   **Every fixed power of the divisor function is bounded by a constant times $n$.**
--
--   For every $m \ge 1$ and $n \ge 1$,
--
--   $$d(n)^{m} \;\le\; \left(\frac{m}{\log 2}\right)^{m\,2^{m}} n ,$$
--
--   where $d(n) = \#\{d : d \mid n\}$.
--
--   Since $d(n) = n^{o(1)}$, the left-hand side is $n^{o(1)}$ for fixed $m$, so the linear bound is
--   far from tight — but it is **explicit**, with a constant depending only on $m$, and that is what
--   makes it usable. The shape is the standard consequence of the divisor bound
--   $d(n) \le C_\varepsilon n^{\varepsilon}$ taken at $\varepsilon = 1/m$: raising to the $m$-th
--   power converts $n^{1/m}$ into $n$, and tracking the constant through the elementary proof of
--   the divisor bound yields the exponent $m2^{m}$.
--
--   Bounds of exactly this form are what allow a divisor-function factor to be absorbed when
--   estimating sums such as $\sum_{n \le x} d(n)^{m} f(n)$: the $d(n)^m$ is traded for a constant
--   at the cost of one power of $n$, after which Cauchy–Schwarz or a trivial bound finishes.
--
--   **Formalization note.** `n.divisors.card` is $d(n)$, cast to $\mathbb{R}$; the exponent
--   $m \cdot 2^{m}$ is a natural number and the base $m/\log 2$ is real.
-- source:
--   Classical; the explicit form of the divisor bound $d(n) \ll_\varepsilon n^\varepsilon$, cf. Iwaniec & Kowalski, *Analytic Number Theory*, §1.6. Lean proof extracted from `Salt/Chen/DivisorBound.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace DivisorBounds

theorem card_divisors_pow_le (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    ((n.divisors.card : ℝ)) ^ m ≤ ((m : ℝ) / Real.log 2) ^ (m * 2 ^ m) * (n : ℝ) := by sorry

end DivisorBounds
