-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_exists_iso
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.BaseChangeAlong.exists_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/ac595d1a-1cd4-56bc-b98e-52d94406275c
-- title:
--   Uniqueness of base change of a Drinfeld datum along g
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field that is an $\mathcal O$-algebra, $\pi \in \mathcal O$, and let $g \colon B \to B'$ be a homomorphism of commutative $\mathcal O$-algebras. Let $Q$ be a Drinfeld datum over $B$ for $\pi$ — that is, families $N_0(x) \le N_1(x)$ of finitely generated $\mathcal O$-submodules of $K^2$ spanning $K^2$ over $K$, indexed by $x \in \operatorname{Spec} B$, with $\pi N_1(x) \subseteq N_0(x)$ and with each membership locus $\{x : v \in N_i(x)\}$ open, together with invertible $B$-modules $T_0, T_1$, maps $\Pi_0 \colon T_0 \to T_1$ and $\Pi_1 \colon T_1 \to T_0$ whose two composites are multiplication by $\pi$, and trivialisations $u_i(x)$ of the stalk of $T_i$ at $x$ by the localised base change of $N_i(x)$, compatible with $\Pi_0$ and with multiplication by $\pi$ — and let $Q', Q''$ be Drinfeld data over $B'$. Assume given two base-change data $W \colon Q \to Q'$ and $W' \colon Q \to Q''$ along $g$; each consists of the equalities $N_i'(x') = N_i(g^{*}x')$ for all $x' \in \operatorname{Spec} B'$, of $g$-semilinear maps $\tau_i \colon T_i \to T_i'$ whose ranges span $T_i'$ over $B'$ and which intertwine the $\Pi_i$, and of clauses asserting that if $u_i(g^{*}x')(1 \otimes v) = t/s$ then $u_i'(x')(1 \otimes v) = \tau_i(t)/g(s)$. The conclusion is that there exists an isomorphism $e$ of Drinfeld data from $Q'$ to $Q''$ (pointwise equal lattice families, $B'$-linear equivalences $e_i \colon T_i' \to T_i''$ commuting with the $\Pi_i$ and with the trivialisations $u_i$) satisfying $e_i(W.\tau_i(t)) = W'.\tau_i(t)$ for all $t \in T_i$ and $i = 0,1$.
--
--   This is the uniqueness half of base change for Drinfeld data: the base change of a Drinfeld datum along a homomorphism of $\mathcal O$-algebras is unique up to a unique isomorphism intertwining the comparison maps, so that the associated functor is well defined on isomorphism classes. It is used in the proof that the comparison maps determine the isomorphism and in the construction of glued modules from overlapping base changes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_exists_iso.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.BaseChangeAlong.exists_iso
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (g : B →ₐ[𝒪] B')
    {Q : DrinfeldDatum (K := K) π B} {Q' Q'' : DrinfeldDatum (K := K) π B'}
    (W : Q.BaseChangeAlong g Q') (W' : Q.BaseChangeAlong g Q'') :
    ∃ e : Q'.Iso Q'', (∀ t, e.τ₀ (W.τ₀ t) = W'.τ₀ t) ∧ (∀ t, e.τ₁ (W.τ₁ t) = W'.τ₁ t) := by sorry
