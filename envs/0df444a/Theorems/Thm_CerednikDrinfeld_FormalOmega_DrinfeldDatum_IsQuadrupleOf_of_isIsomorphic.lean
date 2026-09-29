-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_of_isIsomorphic
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.of_isIsomorphic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/bc02a9f0-b177-5a43-a851-edb43f831ee6
-- title:
--   Invariance of the quadruple relation under isomorphism
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, $K$ a field with an $\mathcal{O}$-algebra structure, $\pi\in\mathcal{O}$, and $B$ a commutative $\mathcal{O}$-algebra. Let $Q,Q'$ be Drinfeld data for $(\pi,B)$ over $K$ (each consisting of two families of full $\mathcal{O}$-lattices $N_0(x)\le N_1(x)$ in $K^2$ indexed by $x\in\operatorname{Spec}B$ with $\pi N_1(x)\subseteq N_0(x)$ and the membership sets open, invertible $B$-modules $T_0,T_1$ with maps $\Pi_0,\Pi_1$ composing to $\pi$, and stalkwise maps $u_i(x)\colon \mathcal{O}_{B,x}\otimes_{\mathcal{O}}N_i(x)\to (T_i)_x$ compatible with inclusion and with multiplication by $\pi$), and let $d$ be a Deligne datum for $(\pi,B)$. Assume $Q$ is the quadruple of $d$, i.e. for every prime $x$ of $B$: the pair $(L_0(x),L_1(x))$ of full lattices satisfies $d$'s edge nondegeneracy condition at $x.\mathrm{asIdeal}$, namely $L_0(x)\subseteq L_1(x)$, $\pi L_1(x)\subseteq L_0(x)$, and for $v\in L_1(x)\setminus L_0(x)$ the element $1\otimes v$ lies outside $d.\mathrm{line}(L_1(x))+x.\mathrm{asIdeal}\cdot\top$, while for $v'\in L_0(x)$ not of the form $\pi w$ with $w\in L_1(x)$ the element $1\otimes v'$ lies outside $d.\mathrm{line}(L_0(x))+x.\mathrm{asIdeal}\cdot\top$; and $\ker u_i(x)$ equals the line of the Deligne datum obtained from $d$ by base change along $B\to\mathcal{O}_{B,x}$ at $L_i(x)$, for $i=0,1$. Assume further that $Q$ and $Q'$ are isomorphic, i.e. the type `Iso Q Q'` is nonempty. Then $Q'$ is likewise the quadruple of $d$.
--
--   This is the well-definedness, on isomorphism classes of Drinfeld quadruples, of the relation used to compare Drinfeld's functor of quadruples with the functor of points of the formal upper half plane in the Čerednik–Drinfeld uniformisation. It is used in the equivalence [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isQuadrupleOf_iff_isIsomorphic`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isQuadrupleOf_iff_isIsomorphic) and in the treatment of Cartier quadruples for the special formal modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_of_isIsomorphic.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.of_isIsomorphic
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    {Q Q' : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B}
    (h : Q.IsQuadrupleOf d) (e : Q.IsIsomorphic Q') : Q'.IsQuadrupleOf d := by sorry
