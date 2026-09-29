-- Prove2me | Theorems.Thm_DivisorBounds_tau_factor_small
-- name    : DivisorBounds.tau_factor_small
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:54:06.64676+00:00
-- url     : https://prove2.me/theorems/24a4f2f7-7a1c-4354-babb-b17508efa75e
-- title:
--   The local factor in the divisor bound
-- statement:
--   **The local estimate behind $d(n) \ll_\varepsilon n^{\varepsilon}$.**
--
--   For a prime power $p^{a}$ with $p \ge 2$ and any $\varepsilon > 0$,
--
--   $$a + 1 \;\le\; \left(1 + \frac{1}{\varepsilon\log 2}\right) p^{\,a\varepsilon} .$$
--
--   The left-hand side $a+1$ is exactly the number of divisors of $p^{a}$, and the right-hand side
--   is $p^{a\varepsilon}$ — the target bound $n^{\varepsilon}$ at $n = p^{a}$ — times a constant
--   depending only on $\varepsilon$.
--
--   This is the **local** form of the divisor bound, and multiplying it over the prime
--   factorisation of $n$ gives the global statement
--   $d(n) \le C_\varepsilon n^{\varepsilon}$ with
--   $C_\varepsilon = \prod_{p < 2^{1/\varepsilon}}(1 + (\varepsilon\log 2)^{-1})$, since the factors
--   at large primes are already $\le 1$.
--
--   The constant is what makes the bound effective. Writing $p^{a\varepsilon} \ge 2^{a\varepsilon} = e^{a\varepsilon\log 2}$
--   and using $e^{x} \ge x$, the right-hand side is at least
--   $(1 + (\varepsilon\log 2)^{-1})\,a\varepsilon\log 2 = a\varepsilon\log 2 + a$, which exceeds
--   $a + 1$ once $a\varepsilon\log 2 \ge 1$; the remaining small-$a$ cases are absorbed by the
--   additive $1$ in the constant.
--
--   **Formalization note.** The exponent $a\varepsilon$ is real, so the power is `Real.rpow`; the
--   hypothesis $p \ge 2$ is what makes $\log p \ge \log 2 > 0$.
-- source:
--   Classical; the local step in the elementary proof of the divisor bound, cf. Iwaniec & Kowalski, *Analytic Number Theory*, §1.6. Lean proof extracted from `Salt/Maynard/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace DivisorBounds

theorem tau_factor_small {p a : ℕ} {ε : ℝ} (hε : 0 < ε) (hp2 : 2 ≤ p) :
    (a : ℝ) + 1 ≤ (1 + (ε * Real.log 2)⁻¹) * (p : ℝ) ^ ((a : ℝ) * ε) := by sorry

end DivisorBounds
