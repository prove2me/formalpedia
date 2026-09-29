-- Prove2me | Theorems.Thm_DirichletCharacters_toArithmeticFunction_prime_pow
-- name    : DirichletCharacters.toArithmeticFunction_prime_pow
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:54:24.020818+00:00
-- url     : https://prove2.me/theorems/d3383a7c-015f-4784-9ea4-213db620f7d4
-- title:
--   A Dirichlet character at a prime power is a power of its value
-- statement:
--   **A Dirichlet character, viewed as an arithmetic function, is determined at prime powers.**
--
--   For a Dirichlet character $\chi$ modulo $N$ and a prime $p$,
--
--   $$\chi(p^{a}) \;=\; \chi(p)^{a} \qquad (a \ge 0).$$
--
--   Dirichlet characters are **completely** multiplicative — $\chi(mn) = \chi(m)\chi(n)$ with no
--   coprimality hypothesis — so the value at a prime power is the corresponding power of the value
--   at the prime, by induction on $a$, with the case $a = 0$ giving $\chi(1) = 1$.
--
--   Complete multiplicativity is exactly what distinguishes characters from general multiplicative
--   arithmetic functions, and it is the reason the Euler factor of $L(s,\chi)$ at $p$ is the
--   geometric series $\sum_a \chi(p)^{a}p^{-as} = (1 - \chi(p)p^{-s})^{-1}$ rather than an
--   uncontrolled power series. Every Euler-product manipulation for Dirichlet $L$-functions reduces
--   to this identity.
--
--   **Formalization note.** `toArithmeticFunction (χ ·)` is the coercion of a character into
--   `ArithmeticFunction ℂ`, which sets the value at $0$ to $0$; the statement is about $p^a$ with
--   $p$ prime, so that convention is not in play.
-- source:
--   Classical; see Apostol, *Introduction to Analytic Number Theory*, §6.8. Lean proof extracted from `Salt/SW/FourFold.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace DirichletCharacters

open ArithmeticFunction DirichletCharacter in
theorem toArithmeticFunction_prime_pow {N : ℕ} (χ : DirichletCharacter ℂ N) {p : ℕ}
    (hp : p.Prime) (a : ℕ) :
    (toArithmeticFunction (χ ·)) (p ^ a) = (χ p) ^ a := by sorry

end DirichletCharacters
