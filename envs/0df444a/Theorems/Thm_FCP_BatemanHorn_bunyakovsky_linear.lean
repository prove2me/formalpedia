-- Prove2me | Theorems.Thm_FCP_BatemanHorn_bunyakovsky_linear
-- name    : FCP.BatemanHorn.bunyakovsky_linear
-- status  : Proved
-- author  : @Himan
-- created : 2026-11-15T03:56:21.383221+00:00
-- url     : https://prove2.me/theorems/836893e4-5a1a-4a60-90c6-344b4c798021
-- title:
--   Bunyakovsky conjecture in degree $1$ (Dirichlet's theorem)
-- statement:
--   **Linear case of Bunyakovsky's conjecture.** Let $f \in \mathbb{Z}[X]$ have positive leading coefficient, be irreducible over $\mathbb{Z}$, and have degree exactly $1$, so $f = aX + b$ with $a > 0$. Then $|f(n)|$ is prime for infinitely many natural numbers $n$.
--
--   Irreducibility of $aX+b$ in $\mathbb{Z}[X]$ forces $\gcd(a,b)=1$, so this is Dirichlet's theorem on primes in the arithmetic progression $b \bmod a$. The Schinzel (no fixed prime divisor) condition is automatic here and is therefore not assumed.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Bunyakovsky.lean); https://en.wikipedia.org/wiki/Bunyakovsky_conjecture (the degree-one case noted there as Dirichlet's theorem)

import Mathlib
import Definitions.Def_FCP_BatemanHorn

open Polynomial

namespace FCP.BatemanHorn

theorem bunyakovsky_linear (f : ℤ[X]) (h_bunyakovsky : BunyakovskyCondition f)
    (h_deg : f.natDegree = 1) :
    {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime}.Infinite := by sorry

end FCP.BatemanHorn
