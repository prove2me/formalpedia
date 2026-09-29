-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_isDomain_holRing_of_liesOverPrime
-- name    : CerednikDrinfeld.Omega.isDomain_holRing_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/dc7bec32-2522-5b34-af1f-617b0476a5d4
-- title:
--   The ring of holomorphic functions on Ω over C_A is a domain
-- statement:
--   Let $r$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ which lies over $r$, in the sense that the image of $r$ in $\overline{\mathbb{Q}}$ belongs to the nonunits of $A$. Write $C_A$ for the completion $A.valuation.Completion$ of $\overline{\mathbb{Q}}$ with respect to the valuation attached to $A$, and let $K_0 = \mathrm{ratClosure}\,A$ be the topological closure of the prime subfield inside $C_A$. Let $\varpi$ be a pseudo-uniformiser of $K_0$ relative to $C_A$, i.e. an element $\varpi \in K_0$ whose image in $C_A$ has valuation strictly between $0$ and $1$ and such that for every nonzero $a \in K_0$ there is $N \in \mathbb{N}$ with $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$. Then the ring $\mathrm{holRing}\,\varpi$ is a domain: the subring of those functions $f$ from the Drinfeld upper half-plane $\mathrm{upperHalfPlane}\,K_0\,C_A$, the complement of the image of $K_0$ in $C_A$, to $C_A$ whose restriction to each affinoid $\mathrm{affinoid}\,\varpi\,n$ is a uniform limit of a uniformly bounded sequence of rational functions without poles on that affinoid, is nontrivial and has no zero divisors.
--
--   This is the identity principle for rigid-analytic functions on Drinfeld's $r$-adic upper half-plane, specialised to the situation actually used in the Čerednik–Drinfeld uniformisation, namely $K_0 = \mathrm{ratClosure}\,A$ inside the completion $C_A$ of $\overline{\mathbb{Q}}$ at a place above $r$, and for an arbitrary pseudo-uniformiser. It supplies the integral-domain hypothesis in the construction of Shimura curve models together with their Hecke towers and interchange data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_isDomain_holRing_of_liesOverPrime.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega ValuationSubring

theorem CerednikDrinfeld.Omega.isDomain_holRing_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (ϖ : PseudoUniformizer ↥(ratClosure A) A.valuation.Completion) :
    IsDomain ↥(holRing ϖ) := by sorry
