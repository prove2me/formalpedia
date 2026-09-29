-- Prove2me | Theorems.Thm_DivisorBounds_card_divisors_cube_root
-- name    : DivisorBounds.card_divisors_cube_root
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:02:35.456966+00:00
-- url     : https://prove2.me/theorems/ba23682b-1375-4791-b965-cd2bad44b241
-- title:
--   An explicit cube-root divisor bound
-- statement:
--   **The divisor function is bounded by an explicit constant times $n^{1/3}$.**
--
--   For every $n \ge 1$,
--
--   $$d(n) \;\le\; \left(\frac{3}{\log 2}\right)^{8} n^{1/3}.$$
--
--   This is the divisor bound $d(n) \ll_\varepsilon n^{\varepsilon}$ specialised to
--   $\varepsilon = 1/3$, with the constant written out. The exponent $1/3$ is far from optimal —
--   the truth is $d(n) = n^{o(1)}$, and even $d(n) \le n^{\varepsilon}$ for every fixed
--   $\varepsilon > 0$ once $n$ is large — but a concrete pair (exponent, constant) valid for
--   **all** $n \ge 1$ is what one can actually substitute into an estimate.
--
--   The constant arises from the local bound $a + 1 \le (1 + (\varepsilon\log 2)^{-1})p^{a\varepsilon}$
--   multiplied over the primes $p < 2^{1/\varepsilon}$, of which there are at most $2^{1/\varepsilon} = 8$
--   when $\varepsilon = 1/3$; each contributes a factor $1 + 3/\log 2 \le 3/\log 2 \cdot$ a constant,
--   giving $(3/\log 2)^{8}$.
--
--   **Formalization note.** `n.divisors.card` is $d(n)$; the power $n^{1/3}$ is `Real.rpow`.
-- source:
--   Classical; the explicit divisor bound, cf. Iwaniec & Kowalski, *Analytic Number Theory*, §1.6. Lean proof extracted from `Salt/Chen/DivisorBound.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace DivisorBounds

theorem card_divisors_cube_root (n : ℕ) (hn : 1 ≤ n) :
    (n.divisors.card : ℝ) ≤ ((3 : ℝ) / Real.log 2) ^ 8 * (n : ℝ) ^ ((1 : ℝ) / 3) := by sorry

end DivisorBounds
