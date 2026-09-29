-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_mem_stratum0_or_mem_stratum1
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.mem_stratum0_or_mem_stratum1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/4016dd9c-1bdd-53a6-92b9-2019e514e606
-- title:
--   The two strata of a Drinfeld datum cover Spec B
-- statement:
--   Let $p$ be a prime, let $B$ be a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure, and assume that the image of $p$ in $B$ is nilpotent. Let $Q$ be a Drinfeld datum over $B$ in the sense of the structure `DrinfeldDatum`, taken with $\mathcal{O}=\mathbb{Z}_p$, $K=\mathbb{Q}_p$ and uniformiser $\pi=p$: thus $Q$ assigns to each point $x$ of $\operatorname{Spec} B$ two $\mathbb{Z}_p$-submodules $N_0(x)\subseteq N_1(x)$ of $\mathbb{Q}_p^2$, each finitely generated and spanning $\mathbb{Q}_p^2$ over $\mathbb{Q}_p$, with $p\,N_1(x)\subseteq N_0(x)$ and with $\{x \mid v\in N_i(x)\}$ open for every $v\in\mathbb{Q}_p^2$; two invertible $B$-modules $T_0,T_1$ together with $B$-linear maps $\Pi_0\colon T_0\to T_1$ and $\Pi_1\colon T_1\to T_0$ whose two composites are both multiplication by $p$; and, at each $x$, $\mathcal{O}_{B,x}$-linear maps $u_0,u_1$ from the base changes of $N_0(x),N_1(x)$ to the stalks of $T_0,T_1$, compatible with the inclusion $N_0(x)\subseteq N_1(x)$ and $\Pi_0$, with multiplication by $p$ and $\Pi_1$, and with the remaining compatibility axioms of the structure. Then every prime $x$ of $B$ lies in `Q.stratum₀` or in `Q.stratum₁`, i.e. either the image of $\Pi_0$ is contained in $x\cdot T_1$ or the image of $\Pi_1$ is contained in $x\cdot T_0$.
--
--   This is the statement that the two strata attached to a Drinfeld datum, on which $\Pi_0$ respectively $\Pi_1$ vanishes modulo the point, cover the whole spectrum of the base; it is the source of the case distinction used in the Čerednik–Drinfeld uniformisation arguments. It is cited in the proof that a rigidified Cartier quadruple is obtained by base change ([`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isBaseChangeAlong`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isBaseChangeAlong)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_mem_stratum0_or_mem_stratum1.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega LT.LatticeTree

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.mem_stratum0_or_mem_stratum1
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [Algebra ℤ_[p] B] (hB : IsNilpotent (p : B))
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (x : PrimeSpectrum B) :
    x ∈ Q.stratum₀ ∨ x ∈ Q.stratum₁ := by sorry
