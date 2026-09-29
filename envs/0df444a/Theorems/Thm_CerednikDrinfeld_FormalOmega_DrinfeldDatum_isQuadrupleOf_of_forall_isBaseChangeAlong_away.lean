-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_of_forall_isBaseChangeAlong_away
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.isQuadrupleOf_of_forall_isBaseChangeAlong_away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/278252c3-b975-5a35-b898-ae1ab7bb5fa3
-- title:
--   Being the quadruple of a Deligne datum is Zariski-local
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field with an $\mathcal O$-algebra structure, $\pi \in \mathcal O$, and $B$ a commutative $\mathcal O$-algebra. Let $k \in \mathbb N$ and $f : \mathrm{Fin}\,k \to B$ be a finite family whose range spans the unit ideal of $B$, so that the basic opens $D(f_i)$ cover $\operatorname{Spec} B$. Let $Q$ be a Drinfeld datum over $B$ for $\pi$ (lattices $N_0(x) \le N_1(x)$ in $K^2$ varying over $x \in \operatorname{Spec} B$, invertible $B$-modules $T_0, T_1$ with maps $\Pi_0, \Pi_1$ composing to $\pi$, and stalkwise maps $u_0(x), u_1(x)$ from the base-changed lattices to the stalks of $T_0, T_1$), and let $d$ be a Deligne datum over $B$ for $\pi$. Suppose given, for each $i$, a Drinfeld datum $Q_i$ over the localisation $B[1/f_i]$ such that (i) $Q$ is a base change of $Q_i$ along $B \to B[1/f_i]$ in the sense of `IsBaseChangeAlong`, i.e. there exists a `BaseChangeAlong` structure: the lattices of $Q_i$ at a prime agree with those of $Q$ at the prime below, together with semilinear maps $T_0 \to (Q_i)_{T_0}$, $T_1 \to (Q_i)_{T_1}$ with spanning images, compatible with $\Pi_0, \Pi_1$ and with $u_0, u_1$; and (ii) $Q_i$ is the quadruple of the base-changed Deligne datum `d.map π` along $B \to B[1/f_i]$. Then $Q$ is the quadruple of $d$: for every prime $x$ of $B$ the predicate `DeligneDatum.EdgeNondegAt` holds for $d$ at $x$ with the pair of full lattices $Q.L_0(x) \le Q.L_1(x)$, and the kernels of $u_0(x)$ and $u_1(x)$ coincide with the lines cut out by the localisation of $d$ at $x$ on the base changes of these two lattices.
--
--   The relation 'is the Drinfeld quadruple of a Deligne datum', in the form used by Boutot–Carayol in the Čerednik–Drinfeld uniformisation, is a pointwise condition on $\operatorname{Spec} B$; this statement records that it may therefore be checked after passing to a finite cover of $\operatorname{Spec} B$ by basic open subsets. It is used in the construction of a Drinfeld datum realising a given Deligne datum, [`CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf_of_forall_away`](thm.html#CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf_of_forall_away).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_of_forall_isBaseChangeAlong_away.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.isQuadrupleOf_of_forall_isBaseChangeAlong_away
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B)
    (Qf : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
    (hbc : ∀ i : Fin k, Q.IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) (Qf i))
    (hQf : ∀ i : Fin k, (Qf i).IsQuadrupleOf (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))))) :
    Q.IsQuadrupleOf d := by sorry
