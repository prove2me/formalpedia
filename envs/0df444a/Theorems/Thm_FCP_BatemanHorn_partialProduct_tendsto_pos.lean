-- Prove2me | Theorems.Thm_FCP_BatemanHorn_partialProduct_tendsto_pos
-- name    : FCP.BatemanHorn.partialProduct_tendsto_pos
-- status  : Open
-- author  : @elem
-- created : 2026-10-12T03:22:51.251949+00:00
-- url     : https://prove2.me/theorems/86db078f-dd5d-41c8-b8e9-9a47494f472c
-- title:
--   Positive convergence of the Bateman–Horn Euler product
-- statement:
--   Let $S$ be a nonempty finite set of distinct integer polynomials. Assume each polynomial is irreducible, has positive leading coefficient and positive degree, and that for every prime $p$ some integer avoids all their roots modulo $p$. Write $k=|S|$ and let $\omega_p(S)$ count the residue classes modulo $p$ at which at least one polynomial vanishes. Then there is a positive real number $C$ such that
--
--   $$\lim_{N\to\infty}\prod_{p<N}(1-1/p)^{-k}(1-\omega_p(S)/p)=C>0.$$
--
--   This is the classical convergence theorem for the singular product, separate from the conjectural prime-counting asymptotic. The primes are taken in increasing order; absolute convergence is not asserted. The source's convention for convergence of a product of positive factors requires its limit to be nonzero.
--
--   This node records a known mathematical result whose Lean proof is still required.
-- source:
--   S. L. Aletheia-Zomlefer, L. Fukshansky and S. R. Garcia, The Bateman-Horn conjecture: Heuristics, History, and Applications, https://www1.cmc.edu/pages/faculty/lenny/papers/bateman-horn.pdf; Theorem 5.4.3, pp. 23–24; positive-product convergence convention in Section 5.1, p. 18; hypotheses in Section 3.6, p. 10.

import Definitions.Def_FCP_BatemanHorn

open Polynomial Filter Topology Asymptotics FCP.BatemanHorn

theorem FCP.BatemanHorn.partialProduct_tendsto_pos
    (polys : Finset ℤ[X]) (h_nonempty : polys.Nonempty)
    (h_bunyakovsky : ∀ f ∈ polys, BunyakovskyCondition f)
    (h_schinzel : SchinzelCondition polys) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (partialProduct polys) atTop (𝓝 C) := by sorry
