-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_of_isBaseChangeAlong
-- name    : CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_of_isBaseChangeAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/fc5c3d8d-a505-5f83-bd17-665d86c85d2f
-- title:
--   Canonical L-maps persist under base change
-- statement:
--   Fix a prime $p$ and commutative rings $B$, $B'$, a ring homomorphism $j$ from $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$ (written [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17)) to $B$, and a ring homomorphism $\varphi : B \to B'$. Let $D$ be a graded Cartier module datum over $(B,j)$: a $W(B)$-module $M$ with additive endomorphisms $F$, $V$, a $W(B)$-linear $\varpi$, and submodules $\mathrm{piece}\,0$, $\mathrm{piece}\,1$ forming a complementary pair, subject to $F(wx)=\sigma(w)F(x)$, $wV(x)=V(\sigma(w)x)$, $V(wF x)=V(w)x$, $FV=p$, commutation of $\varpi$ with $F$ and $V$, $\varpi^2=p$, and the requirement that $F$, $V$, $\varpi$ shift the $\mathbb{Z}/2$-grading by $1$. Assume $D$ is a special Cartier module, i.e. it has a homogeneous $V$-basis $\gamma$ ($\gamma_i \in \mathrm{piece}\,i$, and each $x$ is uniquely $\sum_i \tau(c_i)\gamma_i + V y$ with Teichmüller coefficients) and is $V$-adically complete. Let $D'$ be a second such datum over $(B',\varphi\circ j)$, also special, and let $f : D.M \to D'.M$ be additive and a base change along $\varphi$: it is $\varphi$-semilinear for the Witt module structures, commutes with $F$, $V$ and $\varpi$, preserves each graded piece, and carries some homogeneous $V$-basis of $D$ to one of $D'$. Finally let $L : D.M \to D.\mathrm{NMod}$ be a canonical $L$-map, that is: a Cartier $L$-map ($\sigma$-semilinear, $L(Vx)$ equal to the class of $(\varpi x,0)$, and $D.\mathrm{lambda}\circ L = F$) which moreover admits a lift, namely a $p$-torsion-free ring $S$ with structure map from $\mathbb{Z}_{p^2}$, a surjection $S \twoheadrightarrow B$, a special datum over $S$ with a Cartier $L$-map and a base change to $D$ along which $L$ is induced by the functorial map on $\mathrm{NMod}$. The conclusion is that $D'$ also admits a canonical $L$-map $L' : D'.M \to D'.\mathrm{NMod}$. Only existence is asserted: no compatibility between $L'$ and $L$ along $f$ is claimed here.
--
--   This is the base-change stability of the canonical $L$-map in the Cartier-module description of special formal $\mathcal{O}_D$-modules used in the Čerednik–Drinfel'd uniformisation; the point is that the target datum need not itself come with a $p$-torsion-free lift. It is used in the companion statement [`CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_of_isBaseChangeAlong_of_comp_eq`](thm.html#CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_of_isBaseChangeAlong_of_comp_eq), and thence in the study of rigidified lattices under base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_of_isBaseChangeAlong.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_of_isBaseChangeAlong
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B'] (j : CerednikDrinfeld.Zp2 p →+* B)
    (φ : B →+* B')
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' (φ.comp j)) (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) :
    ∃ L' : D'.M →+ D'.NMod, D'.IsCanonicalLMap L' := by sorry
