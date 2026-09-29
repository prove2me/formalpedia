-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isBaseChangeAlong_of_isLocalization
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isBaseChangeAlong_of_isLocalization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/e3dd2692-a17c-59ad-91ca-86506f25d75d
-- title:
--   Drinfeld data descend along localisations of the base
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field which is an $\mathcal O$-algebra, $\pi\in\mathcal O$, and $B$ a commutative $\mathcal O$-algebra. Let $Q$ be a `DrinfeldDatum` for $\pi$ over $B$ relative to $K$: two families $N_0,N_1$ of $\mathcal O$-submodules of $K^2$ indexed by $\operatorname{Spec} B$, each value being a full lattice (finitely generated with $K$-span all of $K^2$), with $N_0(x)\le N_1(x)$ and $\pi N_1(x)\subseteq N_0(x)$ and with $\{x : v\in N_i(x)\}$ open for every $v\in K^2$; invertible $B$-modules $T_0,T_1$ with $B$-linear maps $\Pi_0:T_0\to T_1$, $\Pi_1:T_1\to T_0$ whose two composites are multiplication by $\pi$; and, for each prime $x$, $B_x$-linear comparison maps $u_i(x):B_x\otimes_{\mathcal O}N_i(x)\to (T_i)_x$ into the stalks, subject to the structure's compatibility conditions with the inclusion $N_0(x)\subseteq N_1(x)$, with multiplication by $\pi$, and the further conditions of the structure (summarised here). Let $S$ be a submonoid of $B$ and let $C$ be a commutative $\mathcal O$-algebra and $B$-algebra, compatibly, which is a localisation of $B$ at $S$. Then there is a `DrinfeldDatum` $Q'$ for $\pi$ over $C$ with `Q.IsBaseChangeAlong` the canonical $\mathcal O$-algebra map $B\to C$ and $Q'$, i.e. there exists a `BaseChangeAlong` datum: the lattice functions of $Q'$ at a prime $x'$ of $C$ agree with those of $Q$ at the point of $\operatorname{Spec} B$ below $x'$, together with maps $\tau_0:Q.T_0\to Q'.T_0$ and $\tau_1:Q.T_1\to Q'.T_1$ semilinear over $B\to C$ whose ranges span over $C$, commuting with $\Pi_0$ and $\Pi_1$, and transporting the stalk maps $u_0,u_1$ in the sense recorded by that structure.
--
--   This is the transition map of Drinfeld's functor of quadruples along a localisation of the base ring, phrased as the existence of a datum over $C$ standing in the relation "is a base change of" to the given datum over $B$. It is used when restricting a datum to distinguished opens, for instance in the passage from a Deligne datum to a Drinfeld datum, in the covering statements for quadruples, and in the glueing of the modules $T_0,T_1$ from data matching on overlaps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isBaseChangeAlong_of_isLocalization.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isBaseChangeAlong_of_isLocalization
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] (Q : DrinfeldDatum (K := K) π B) (S : Submonoid B)
    (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] [IsLocalization S C] :
    ∃ Q' : DrinfeldDatum (K := K) π C, Q.IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 B C) Q' := by sorry
