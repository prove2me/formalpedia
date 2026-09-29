-- Prove2me | Theorems.Thm_FCP_BatemanHorn_bunyakovsky_conjecture
-- name    : FCP.BatemanHorn.bunyakovsky_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T19:53:05.609119+00:00
-- url     : https://prove2.me/theorems/ba4d44ce-6025-4f73-8ac7-3a34173d589f
-- title:
--   Bunyakovsky conjecture
-- statement:
--   **Bunyakovsky's conjecture.** Let $f \in \mathbb{Z}[X]$ have positive leading coefficient, degree at least $1$, and be irreducible over $\mathbb{Z}$, and assume that no prime divides all the values $f(n)$ (the Schinzel condition for the one-element family $\{f\}$). Then $f(n)$ is prime in absolute value for infinitely many natural numbers $n$.
--
--   For $\deg f = 1$ this is Dirichlet's theorem on primes in arithmetic progressions; not a single case with $\deg f \ge 2$ is known, $f = X^2 + 1$ being the classical example.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Bunyakovsky.lean); https://en.wikipedia.org/wiki/Bunyakovsky_conjecture

import Mathlib
import Definitions.Def_FCP_BatemanHorn

open Polynomial

namespace FCP.BatemanHorn

theorem bunyakovsky_conjecture (f : ℤ[X]) (h_bunyakovsky : BunyakovskyCondition f)
    (h_schinzel : SchinzelCondition {f}) :
    {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime}.Infinite := by sorry

end FCP.BatemanHorn
