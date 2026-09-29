-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_baseChange_of_torsionFree
-- name    : CerednikDrinfeld.GradedCartierModuleData.exists_isSpecialCartierModule_and_baseChange_of_torsionFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/04cbb1ac-71f9-553e-9760-119f302d5b3b
-- title:
--   Base change of a special graded Cartier module over a p-torsion-free ring
-- statement:
--   Let $p$ be a prime, let $S$ and $T$ be commutative rings, let $j_S \colon \mathbb{Z}_{p^2} \to S$ and $j_T \colon \mathbb{Z}_{p^2} \to T$ be ring homomorphisms, where $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$ is [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17), and let $\iota \colon S \to T$ be a ring homomorphism. Assume $S$ is $p$-torsion-free, in the form that $ps = 0$ implies $s = 0$ for $s \in S$. Let $D_S$ be a graded Cartier module datum over $(S, j_S)$: a $W(S)$-module $M$ with additive endomorphisms $F$ and $V$, a $W(S)$-linear $\varpi$, and a family of submodules indexed by $\mathrm{Fin}\ 2$, subject to $F(w \cdot x) = \sigma(w) \cdot F x$, $w \cdot Vx = V(\sigma(w) \cdot x)$, $V(w \cdot Fx) = V(w) \cdot x$, $F V = p$, commutation of $\varpi$ with $F$ and $V$, $\varpi^2 = p$, complementarity of the two pieces, and shifting of the grading by one under $V$, $F$ and $\varpi$. Assume $D_S$ is special: it admits a homogeneous $V$-basis $\gamma$ (with $\gamma_i$ in piece $i$, every $x$ uniquely of the form $\sum_i \tau(c_i) \cdot \gamma_i + V y$ with $c \in S^2$, $\tau$ the Teichmüller lift) and is $V$-adically complete (every sequence $(x_m)$ in $M$ has a unique sum $s$, meaning that for each $N$ the element $s - \sum_{m<N} V^m x_m$ lies in $V^N M$). Then there exist a graded Cartier module datum $D_T$ over $(T, j_T)$ which is special, and an additive map $g \colon M_{D_S} \to M_{D_T}$ which is a base change along $\iota$: it is semilinear for `WittVector.map` $\iota$, commutes with $F$, $V$ and $\varpi$, sends piece $i$ into piece $i$, and carries some homogeneous $V$-basis of $D_S$ to a homogeneous $V$-basis of $D_T$.
--
--   This is the existence of the completed base change $W(T) \,\widehat{\otimes}\, M_S$ of a special graded Cartier module along an arbitrary ring map, in the setting of Boutot–Carayol's treatment of the Čerednik–Drinfeld uniformisation, with an arbitrary choice of $\mathbb{Z}_{p^2}$-structure on the target. It supports the comparison results for canonical $L$-maps, such as [`CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.eq_of_isNilpotent`](thm.html#CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.eq_of_isNilpotent) and its companions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_baseChange_of_torsionFree.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.exists_isSpecialCartierModule_and_baseChange_of_torsionFree
    (p : ℕ) [Fact p.Prime] {S T : Type} [CommRing S] [CommRing T]
    {jS : CerednikDrinfeld.Zp2 p →+* S} (jT : CerednikDrinfeld.Zp2 p →+* T) (ι : S →+* T)
    (hS : ∀ s : S, (p : S) * s = 0 → s = 0)
    (DS : CerednikDrinfeld.GradedCartierModuleData p S jS) (hDS : DS.IsSpecialCartierModule) :
    ∃ DT : CerednikDrinfeld.GradedCartierModuleData p T jT,
      DT.IsSpecialCartierModule ∧
      ∃ g : DS.M →+ DT.M, CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' ι DS DT g := by sorry
