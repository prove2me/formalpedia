-- Prove2me | Theorems.Thm_FCP_BatemanHorn_bunyakovsky_degree_ge_two
-- name    : FCP.BatemanHorn.bunyakovsky_degree_ge_two
-- status  : Open
-- author  : @Himan
-- created : 2026-11-15T03:56:18.89723+00:00
-- url     : https://prove2.me/theorems/a09bc382-3819-4646-8b77-cd7d27eaa949
-- title:
--   Bunyakovsky conjecture in degree $\ge 2$
-- statement:
--   **Bunyakovsky's conjecture, nonlinear case.** Let $f \in \mathbb{Z}[X]$ have positive leading coefficient, be irreducible over $\mathbb{Z}$, and have degree at least $2$, and assume that no prime divides all the values $f(n)$ (the Schinzel condition for the one-element family $\{f\}$). Then $|f(n)|$ is prime for infinitely many natural numbers $n$.
--
--   This is the open part of Bunyakovsky's conjecture: it is not known for any single polynomial of degree $\ge 2$, with $f = X^2+1$ the classical example. Together with the degree-one case (Dirichlet's theorem) it gives the full conjecture.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Bunyakovsky.lean); https://en.wikipedia.org/wiki/Bunyakovsky_conjecture

import Mathlib
import Definitions.Def_FCP_BatemanHorn

open Polynomial

namespace FCP.BatemanHorn

theorem bunyakovsky_degree_ge_two (f : ℤ[X]) (h_bunyakovsky : BunyakovskyCondition f)
    (h_schinzel : SchinzelCondition {f}) (h_deg : 2 ≤ f.natDegree) :
    {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime}.Infinite := by sorry

end FCP.BatemanHorn
