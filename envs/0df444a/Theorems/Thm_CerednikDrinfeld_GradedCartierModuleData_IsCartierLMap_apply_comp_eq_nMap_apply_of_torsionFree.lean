-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_apply_comp_eq_nMap_apply_of_torsionFree
-- name    : CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.apply_comp_eq_nMap_apply_of_torsionFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/be72e9f3-14bc-503f-b783-ae1913b2a68d
-- title:
--   Base change compatibility of Cartier L-maps, p-torsion-free target
-- statement:
--   Fix a prime $p$ and commutative rings $S$, $T$ equipped with ring maps $j_S, j_T$ from $W(\mathbb{F}_{p^2})$, and let $g\colon S\to T$ be a ring homomorphism with $T$ having no $p$-torsion, in the form: $p\,t=0$ implies $t=0$ for all $t\in T$. Let $D$ and $D'$ be graded Cartier module data over $S$ and $T$ respectively, i.e. modules $M$ over $W(S)$, resp. $M'$ over $W(T)$, carrying additive endomorphisms $F$, $V$, a linear $\varpi$ and a decomposition into two complementary submodules indexed by $\mathrm{Fin}\,2$, subject to the usual semilinearity, $FV=p$, $\varpi^2=p$, commutation and degree-shift axioms; assume both are special, i.e. each admits a homogeneous $V$-basis $\gamma$ ($\gamma_i$ in the $i$-th piece, every element uniquely of the form $\sum_i \tau(c_i)\gamma_i+V y$ with Teichmüller lifts $\tau$) and is $V$-adically complete. Let $f\colon M\to M'$ be additive and a base change along $g$: $W(g)$-semilinear, commuting with $F$, $V$ and $\varpi$, degree-preserving, and carrying some homogeneous $V$-basis of $M$ to one of $M'$. Let $L\colon M\to N(M)$ and $L'\colon M'\to N(M')$ be Cartier $L$-maps, where $N(M)=(M\times M^{\sigma})/\mathrm{nRel}$: thus $L(w\cdot x)=\sigma(w)\cdot L(x)$, $L(Vx)$ is the class of $(\varpi x,0)$, and $\lambda\circ L=F$, and similarly for $L'$. The conclusion is that for every $x\in M$, $L'(f(x))=N(f)(L(x))$, where $N(f)$ is the map on quotients induced by $f\times f^{\sigma}$ using that $f$ commutes with $V$ and $\varpi$.
--
--   This is the base change compatibility of the $L$-maps attached to special formal $\mathcal{O}$-modules in the Cherednik–Drinfeld uniformisation, in the torsion-free setting of Boutot–Carayol, II (3.6), (3.8). It is used to transport an $L$-map along refinements of a torsion-free lift, and so feeds into the uniqueness and naturality statements for the canonical $L$-map, including the results on canonical $L$-maps over nilpotent bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_apply_comp_eq_nMap_apply_of_torsionFree.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.apply_comp_eq_nMap_apply_of_torsionFree
    (p : ℕ) [Fact p.Prime] {S T : Type} [CommRing S] [CommRing T]
    {jS : CerednikDrinfeld.Zp2 p →+* S} {jT : CerednikDrinfeld.Zp2 p →+* T}
    (g : S →+* T) (hT : ∀ t : T, (p : T) * t = 0 → t = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p S jS) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p T jT) (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' g D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L) (L' : D'.M →+ D'.NMod) (hL' : D'.IsCartierLMap L') :
    ∀ x : D.M, L' (f x) = D.nMap D' f hf.2.2.1 hf.2.2.2.1 (L x) := by sorry
