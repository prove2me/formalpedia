-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_deligneDatum_unique
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.deligneDatum_unique
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/708db8e0-55d7-5041-ad45-36063d389681
-- title:
--   Uniqueness of the Deligne datum of a Drinfeld quadruple
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation domain with fraction field $K$ (given as an $\mathcal{O}$-algebra which is a fraction ring of $\mathcal{O}$), let $\pi \in \mathcal{O}$ be irreducible, and let $B$ be a commutative $\mathcal{O}$-algebra. Let $Q$ be a Drinfeld datum over $B$ relative to $\pi$ — a pair of full $\mathcal{O}$-lattices $N_0(x) \le N_1(x)$ in $K^2$ depending on $x \in \operatorname{Spec} B$ with $\pi N_1(x) \subseteq N_0(x)$ and open membership loci, invertible $B$-modules $T_0, T_1$ with maps $\Pi_0, \Pi_1$ composing to multiplication by $\pi$ on either side, and $B_x$-linear maps $u_i(x) : B_x \otimes_{\mathcal{O}} N_i(x) \to (T_i)_x$ compatible with the inclusions, with multiplication by $\pi$ and with $\Pi_0, \Pi_1$ — and let $d, d'$ be Deligne data over $B$ relative to $\pi$, that is, assignments $M \mapsto \operatorname{line}(M) \subseteq B \otimes_{\mathcal{O}} M$ of $B$-submodules with invertible quotient for every full lattice $M$ in $K^2$, monotone under inclusions of lattices, equivariant for scalar homotheties, and satisfying the nondegeneracy condition at every prime of $B$. Assume that $Q$ is a quadruple of $d$ and also a quadruple of $d'$: for each prime $x$ of $B$ the pair $(Q.L_0(x), Q.L_1(x))$ of full lattices attached to $Q$ at $x$ satisfies the edge nondegeneracy condition for the datum in question at the prime $x$ (the first lattice contained in the second, $\pi$ times the second contained in the first, and for $v$ in the larger lattice outside the smaller one, resp. $v'$ in the smaller lattice not divisible by $\pi$ in the larger one, the element $1 \otimes v$, resp. $1 \otimes v'$, avoids the sum of the corresponding line with $x \cdot \top$), and the kernels of $u_0(x)$ and $u_1(x)$ coincide with the lines at $Q.L_0(x)$, resp. $Q.L_1(x)$, of the Deligne datum base changed along $B \to B_x$. Then $d' = d$.
--
--   This is the well-definedness of the comparison from Drinfeld's functor of quadruples to the functor of points of the formal upper half plane in the Deligne-datum (kernel-line) model: the relation "is the quadruple of" is the graph of a partial map, so a Drinfeld quadruple determines at most one Deligne datum. It is used in the representability statement for Drinfeld data over rings with nilpotent structure and in the comparison of Cartier quadruples with Drinfeld quadruples.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_deligneDatum_unique.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.deligneDatum_unique
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    {Q : DrinfeldDatum (K := K) π B} {d d' : DeligneDatum (K := K) π B}
    (h : Q.IsQuadrupleOf d) (h' : Q.IsQuadrupleOf d') : d' = d := by sorry
