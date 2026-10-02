-- Prove2me | Theorems.Thm_ChebotarevDensity_kronecker_rootCount
-- name    : ChebotarevDensity.kronecker_rootCount
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-01T14:26:30.907376+00:00
-- url     : https://prove2.me/theorems/f121b3a4-800e-472f-84d5-58f4697de972
-- title:
--   Kronecker: roots of an irreducible polynomial modulo p average to 1
-- statement:
--   Let $g\in\mathbb Z[X]$ be a monic polynomial that is irreducible over $\mathbb Q$. For a prime $p$ let $N_g(p)$ denote the number of roots of $g \bmod p$ in $\mathbb F_p$. Then there is a constant $C$ such that, for all real $s>1$ sufficiently close to $1$,
--   $$\Bigl|\ \sum_{p\ \text{prime}}N_g(p)\,p^{-s}-\log\frac1{s-1}\ \Bigr|\le C .$$
--
--   In words: the number of roots of an irreducible integer polynomial modulo $p$ averages to $1$ over the primes $p$, in the sense of analytic density. This is Kronecker's observation behind Frobenius's density theorem; it says that the number of irreducible factors of an integer polynomial over $\mathbb Q$ equals the average number of its roots modulo $p$.
--
--   **Formalization Note** $N_g(p)$ is `rootCount g p`, defined in the auxiliary definitions file.
-- source:
--   Serre, A Course in Arithmetic, Ch. VI; Lang, Algebraic Number Theory, Ch. VIII §4 (Dedekind zeta functions and densities); Neukirch, Algebraic Number Theory, Ch. VII §13 (density of prime ideals; Frobenius density theorem)

import Definitions.Def_ChebotarevDensity_Aux

open Polynomial NumberField

namespace ChebotarevDensity

theorem kronecker_rootCount (g : ℤ[X]) (hg : g.Monic)
    (hirr : Irreducible (g.map (Int.castRingHom ℚ))) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1),
      |(∑' p : {p : ℕ // p.Prime}, (rootCount g p : ℝ) * ((p : ℕ) : ℝ) ^ (-s)) -
        Real.log (1 / (s - 1))| ≤ C := by sorry

end ChebotarevDensity
