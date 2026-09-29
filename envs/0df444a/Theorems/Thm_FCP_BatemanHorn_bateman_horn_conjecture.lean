-- Prove2me | Theorems.Thm_FCP_BatemanHorn_bateman_horn_conjecture
-- name    : FCP.BatemanHorn.bateman_horn_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T19:13:26.596179+00:00
-- url     : https://prove2.me/theorems/affe3851-b008-4dc6-a005-f55d8f117771
-- title:
--   Bateman--Horn conjecture
-- statement:
--   **The Bateman--Horn conjecture.** Let $S = \{f_1, \dots, f_k\}$ be a nonempty finite set of distinct polynomials in $\mathbb{Z}[X]$, each with positive leading coefficient, degree at least $1$ and irreducible over $\mathbb{Z}$, and assume the Schinzel condition: for every prime $p$ some integer $n$ has $p \nmid f_1(n)\cdots f_k(n)$.
--
--   Then the truncated Euler products
--   $$P_N(S) = \prod_{p<N}\left(1-\tfrac1p\right)^{-k}\left(1-\tfrac{\omega_p(S)}{p}\right)$$
--   converge, as $N \to \infty$, to a strictly positive constant $C$ (the Bateman--Horn constant), and the counting function $\pi_S(x)$ of the integers $n \le x$ at which all $f_i$ are simultaneously prime in absolute value satisfies the asymptotic
--   $$\pi_S(x) \sim \frac{C}{D}\,\frac{x}{(\log x)^k}, \qquad D = \prod_{i} \deg f_i.$$
--
--   This is the quantitative form of Schinzel's hypothesis H; it contains the twin prime conjecture ($f_1 = X$, $f_2 = X+2$) and the Bunyakovsky conjecture as special cases, and no case with $k \ge 1$ and $\deg f_1 \ge 2$ is known.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/BatemanHornConjecture.lean); https://en.wikipedia.org/wiki/Bateman%E2%80%93Horn_conjecture

import Mathlib
import Definitions.Def_FCP_BatemanHorn

open Polynomial Filter Topology Asymptotics

namespace FCP.BatemanHorn

theorem bateman_horn_conjecture (polys : Finset ℤ[X]) (h_nonempty : polys.Nonempty)
    (h_bunyakovsky : ∀ f ∈ polys, BunyakovskyCondition f)
    (h_schinzel : SchinzelCondition polys) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (partialProduct polys) atTop (𝓝 C) ∧
      (fun x : ℝ => (countSimultaneousPrimes polys x : ℝ)) ~[atTop]
        (fun x : ℝ => C / degreesProduct polys * x / (Real.log x) ^ polys.card) := by sorry

end FCP.BatemanHorn
