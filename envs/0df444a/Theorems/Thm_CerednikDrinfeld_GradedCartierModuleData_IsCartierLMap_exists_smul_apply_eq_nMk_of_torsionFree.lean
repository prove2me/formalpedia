-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_exists_smul_apply_eq_nMk_of_torsionFree
-- name    : CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.exists_smul_apply_eq_nMk_of_torsionFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/d05078b3-bd81-529f-a74e-fb0b85064938
-- title:
--   The L-map on a V-basis vector over a p-torsion-free base
-- statement:
--   Let $p$ be a prime, $S$ a commutative ring with a ring homomorphism $j_S\colon W(\mathbb F_{p^2})\to S$, and assume $S$ has no $p$-torsion, i.e. $ps=0$ implies $s=0$ for $s\in S$. Let $D$ be a graded Cartier module datum over $S$: a $W(S)$-module $M$ together with additive endomorphisms $F$ (`frobenius`) and $V$ (`verschiebung`), a $W(S)$-linear endomorphism $\Pi$ (`varpi`), and submodules $M_0,M_1$ forming a complementary pair, subject to the usual relations ($F$ is $\sigma$-semilinear, $w\,Vx=V(\sigma(w)x)$, $V(w\,Fx)=V(w)\,x$, $FV=p$, $\Pi$ commutes with $F$ and $V$, $\Pi^2=p$, and $F$, $V$, $\Pi$ each shift the grading by one). Let $\gamma_0,\gamma_1$ be a homogeneous $V$-basis: $\gamma_i\in M_i$ and every $x\in M$ is uniquely $\sum_i[c_i]\gamma_i+Vm$ with $c\in S^2$, $m\in M$. Let $L\colon M\to N(M)$ be an additive map which is a Cartier $L$-map, i.e. $L(w\cdot x)=\sigma(w)\cdot L(x)$, $L(Vx)=((\Pi x,0))$, and $\lambda(L(x))=F(x)$, where $N(M)$ is the quotient of $M\times M^{(\sigma)}$ by the relation submodule, $((\cdot,\cdot))$ denotes the induced map `nMk` from $M\times M$, and $\lambda((y,z))=\Pi y+Vz$. Fix $i\in\mathbb Z/2$. Then there exist $a,d\in S$, elements $x,u,v,u',m\in M$ and $\varepsilon\in W(S)$ with $\Pi\gamma_i=[a]\gamma_{i+1}+Vx$, $p=[p]+V\varepsilon$ in $W(S)$, $\varepsilon\cdot L(\gamma_i)=((x+u,v))$, $u=[a^{p-1}d]\gamma_i+Vu'$, and $\Pi u+Vv=[a]m$, where $[\,\cdot\,]$ is the Teichmüller lift.
--
--   This is the computation over a $p$-torsion-free lift underlying Lemme (4.2) of Boutot–Carayol's treatment of the Čerednik–Drinfeld uniformisation: expanding $\Pi^2\gamma_i=p\gamma_i$ in the $V$-basis and using injectivity of $\lambda$ to locate $\varepsilon L(\gamma_i)$ in the image of `nMk`. It is used in the analysis of the canonical $L$-map attached to a special formal $\mathcal O_D$-module, in particular by [`CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP`](thm.html#CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP) and [`CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_verschiebungInt_eq_endAct_varpiEnd`](thm.html#CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_verschiebungInt_eq_endAct_varpiEnd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_exists_smul_apply_eq_nMk_of_torsionFree.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.exists_smul_apply_eq_nMk_of_torsionFree
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (jS : Zp2 p →+* S)
    (hS : ∀ s : S, (p : S) * s = 0 → s = 0)
    (D : GradedCartierModuleData p S jS) (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L) (i : Fin 2) :
    ∃ (a d : S) (x u v u' m : D.M) (ε : WittVector p S),
      D.varpi (γ i) = WittVector.teichmuller p a • γ (i + 1) + D.verschiebung x ∧
      ((p : ℕ) : WittVector p S) = WittVector.teichmuller p (p : S) + WittVector.verschiebung ε ∧
      ε • L (γ i) = D.nMk (x + u, v) ∧
      u = WittVector.teichmuller p (a ^ (p - 1) * d) • γ i + D.verschiebung u' ∧
      D.varpi u + D.verschiebung v = WittVector.teichmuller p a • m := by sorry
