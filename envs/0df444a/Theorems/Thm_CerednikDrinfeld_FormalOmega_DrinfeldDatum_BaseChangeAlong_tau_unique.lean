-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_tau_unique
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.BaseChangeAlong.tau_unique
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/840486dd-5cd9-579d-abc2-8f2c6ebd0a01
-- title:
--   Uniqueness of base-change comparison maps τ₀,τ₁
-- statement:
--   Fix a commutative ring $\mathcal{O}$, a field $K$ that is an $\mathcal{O}$-algebra, an element $\pi \in \mathcal{O}$, two commutative $\mathcal{O}$-algebras $B$ and $B'$, and an $\mathcal{O}$-algebra homomorphism $g : B \to B'$. Let $Q$ be a Drinfeld datum over $B$ for $\pi$ and $K$, and $Q'$ one over $B'$: each consists of two families of finitely generated $\mathcal{O}$-submodules of $K^2$ spanning $K^2$ over $K$, indexed by the prime spectrum, with $N_0(x) \le N_1(x)$, $\pi N_1(x) \subseteq N_0(x)$ and the membership loci open; together with invertible modules $T_0, T_1$ over the base, linear maps $\Pi_0 : T_0 \to T_1$ and $\Pi_1 : T_1 \to T_0$ with both composites equal to multiplication by $\pi$, and stalkwise trivialisations $u_i(x)$ from $B_x \otimes_{\mathcal{O}} N_i(x)$ to the stalk of $T_i$ at $x$, compatible with $\Pi_0$ and with multiplication by $\pi$. Let $W$ and $W'$ be two witnesses that $Q'$ is the base change of $Q$ along $g$, i.e. two records consisting of the identifications $N_i'(x') = N_i(\mathrm{comap}\,g\,(x'))$, $g$-semilinear maps $\tau_0 : Q.T_0 \to Q'.T_0$ and $\tau_1 : Q.T_1 \to Q'.T_1$ whose images span over $B'$, commuting with $\Pi_0$ and $\Pi_1$, and satisfying the stalkwise compatibility of the trivialisations $u_0$, $u_1$ with $\tau_0$, $\tau_1$. The conclusion is that $W.\tau_0$ and $W'.\tau_0$ agree at every element, and likewise $W.\tau_1$ and $W'.\tau_1$.
--
--   This is the rigidity statement that a base-change witness for a Drinfeld datum is unique on the nose once the source datum, the algebra map and the target datum are fixed: the comparison maps carry no further choice. It is used when the modules $T_0, T_1$ of data given on a cover are glued, where the diagonal and cocycle conditions must be checked for chains of base-change comparisons; it is cited by [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_gluedModules_of_baseChangeAlong_overlap`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_gluedModules_of_baseChangeAlong_overlap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_tau_unique.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.BaseChangeAlong.tau_unique
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (g : B →ₐ[𝒪] B')
    {Q : DrinfeldDatum (K := K) π B} {Q' : DrinfeldDatum (K := K) π B'}
    (W W' : Q.BaseChangeAlong g Q') :
    (∀ t, W.τ₀ t = W'.τ₀ t) ∧ (∀ t, W.τ₁ t = W'.τ₁ t) := by sorry
