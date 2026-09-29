-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/238fd875-44e3-5655-ab77-b8e9a5aa32d6
-- title:
--   Base change along f is invariant under isomorphism of the target datum
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field equipped with an $\mathcal O$-algebra structure, $\pi \in \mathcal O$, and let $B$, $B'$ be commutative $\mathcal O$-algebras with $f : B \to B'$ a homomorphism of $\mathcal O$-algebras. Let $Q$ be a Drinfeld datum over $B$ for $\pi$ (a pair of assignments $x \mapsto N_0(x), N_1(x)$ of full $\mathcal O$-lattices in $K^2$ on $\operatorname{Spec} B$ with $N_0(x) \le N_1(x)$, $\pi N_1(x) \subseteq N_0(x)$ and the membership loci open, invertible $B$-modules $T_0, T_1$ with $B$-linear maps $\Pi_0, \Pi_1$ between them whose two composites are multiplication by $\pi$, together with trivialisations $u_0, u_1$ of the stalks at each point compatible with the inclusion and with multiplication by $\pi$), and let $Q', Q''$ be Drinfeld data over $B'$ for $\pi$. Assume `Q.IsBaseChangeAlong f Q'`, i.e. there is a witness consisting of the equalities $Q'.N_i(x') = Q.N_i(\mathrm{pointUnder}\, f\, x')$ for $i = 0,1$ and all primes $x'$ of $B'$, $f$-semilinear maps $\tau_i : Q.T_i \to Q'.T_i$ whose ranges span $Q'.T_i$ over $B'$, commuting with $\Pi_0$ and $\Pi_1$, and satisfying the stalk clauses transporting an identity $Q.u_i(1 \otimes v) = \mathrm{mk}(t,s)$ to $Q'.u_i(1 \otimes v) = \mathrm{mk}(\tau_i t, f(s))$. Assume further that $Q'$ and $Q''$ are isomorphic, in the sense that `Iso Q' Q''` is nonempty. Then `Q.IsBaseChangeAlong f Q''` holds.
--
--   Base change of Drinfeld data along an $\mathcal O$-algebra map is only defined up to isomorphism of the target datum, and this transport lemma records that the relation is stable under such isomorphisms; no hypothesis on $f$ is needed. It is used in the Zariski gluing of Drinfeld data and in the construction of a Drinfeld datum attached to a Deligne datum from local pieces, where a base change must be replaced by an isomorphic datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    {Q : DrinfeldDatum (K := K) π B} {Q' Q'' : DrinfeldDatum (K := K) π B'}
    (h : Q.IsBaseChangeAlong f Q') (e : Q'.IsIsomorphic Q'') : Q.IsBaseChangeAlong f Q'' := by sorry
