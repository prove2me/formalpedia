-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_mem_etaPiece_add_eq
-- name    : CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_mem_etaPiece_add_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/db6cd1be-6754-5223-bbe3-2a7e13eaf42f
-- title:
--   Graded splitting of the φ_L-fixed subgroup η(L)
-- statement:
--   Fix a prime $p$, a commutative ring $B$ and a ring homomorphism $j$ from $\mathbb{W}(\mathbb{F}_{p^2})$ to $B$, and let $D$ be a graded Cartier module datum over $(B,j)$: a module $D.M$ over the Witt ring $\mathbb{W}(p,B)$ equipped with additive endomorphisms $F$ and $V$ and a $\mathbb{W}(p,B)$-linear $\varpi$ satisfying the usual semilinearity and composition identities ($F(w\cdot x)=\sigma(w)\cdot F x$, $w\cdot Vx = V(\sigma(w)\cdot x)$, $V(w\cdot Fx)=V(w)\cdot x$, $FV=p$, $\varpi$ commuting with $F$ and $V$, $\varpi^2=p$), together with two complementary submodules $D.\mathrm{piece}\,0$, $D.\mathrm{piece}\,1$ each of which is carried into the other by $F$, $V$ and $\varpi$. Let $L : D.M \to D.\mathrm{NMod}$ be an additive map which is a canonical $L$-map: it is a Cartier $L$-map ($\sigma$-semilinear, $L(Vx)$ equal to the class of $(\varpi x,0)$, and $\lambda \circ L = F$) and it descends from a Cartier $L$-map on a special graded Cartier module datum over a $p$-torsion-free ring surjecting onto $B$ via a base change map, in the sense of the lifting clause of `IsCanonicalLMap`. Let $z$ be an element of $D.\mathrm{NMod}$ lying in $D.\mathrm{eta}\,L$, i.e. fixed by the endomorphism `D.phi L`, where the grading on $D.\mathrm{NMod}$ is given by the subgroups $D.\mathrm{nPiece}\,i$, the images under the quotient map of $D.\mathrm{piece}\,i \times D.\mathrm{piece}\,i$. Then $z = z_0 + z_1$ with $z_i$ in $D.\mathrm{etaPiece}\,L\,i = D.\mathrm{eta}\,L \cap D.\mathrm{nPiece}\,i$.
--
--   This is the statement that the fixed module $\eta(L)$ of the $\varphi_L$-operator on $N(M)$ is graded by the two-term grading of $N(M)$, the degree bookkeeping needed for the Čerednik–Drinfeld lattices. It is used to transport $\eta$-sections between a datum and its reduction componentwise, and to place constructed sections in the degree-zero part, in the $p$-adic uniformisation input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_mem_etaPiece_add_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_mem_etaPiece_add_eq
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (z : D.NMod) (hz : z ∈ D.eta L hL.isCartierLMap.map_verschiebung) :
    ∃ z₀ ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung 0,
      ∃ z₁ ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung 1, z = z₀ + z₁ := by sorry
