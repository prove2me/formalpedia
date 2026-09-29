-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_apply_mem_nPiece
-- name    : CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.apply_mem_nPiece
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/b4685c8c-dee5-5aab-956a-d9031cbff277
-- title:
--   Canonical L-maps preserve the ℤ/2-grading
-- statement:
--   Fix a prime $p$, a commutative ring $B$ and a ring homomorphism $j$ from $\mathbb{W}(\mathbb{F}_{p^2})$ to $B$, and let $D$ be a graded Cartier module datum over $(B,j)$: a module $M$ over the Witt vectors $\mathbb{W}(B)$ equipped with additive endomorphisms $F$ and $V$, a $\mathbb{W}(B)$-linear $\varpi$, and two submodules $M_0, M_1$ forming a complementary pair, subject to $F(wx)=\sigma(w)F(x)$, $wV(x)=V(\sigma(w)x)$, $V(wF(x))=V(w)x$, $FV=p$, commutation of $\varpi$ with $F$ and $V$, $\varpi^2=p$, and the condition that each of $F$, $V$, $\varpi$ carries $M_i$ into $M_{i+1}$. Let $L$ be an additive map from $M$ to $N(M)=(M\times \Sigma)/\mathrm{nRel}$, where $\Sigma$ is $M$ with the $\mathbb{W}(B)$-action twisted by Frobenius. Assume $L$ is a canonical $L$-map, that is: $L$ is a Cartier $L$-map ($L(wx)=\sigma(w)L(x)$, $L(V x)$ is the class of $(\varpi x,0)$, and $\lambda\circ L=F$), and $L$ admits a lift — there are a commutative ring $S$ with a map $jS$, a surjection $\varphi : S \to B$, $S$ having no $p$-torsion, a datum $D_\ell$ over $(S,jS)$ which is special (it has a homogeneous $V$-basis and is $V$-adically complete), an additive $f : D_\ell.M \to M$ which is a base change along $\varphi$, and a Cartier $L$-map $L_\ell$ on $D_\ell$ with $L\circ f = N(f)\circ L_\ell$. Then for every $i \in \{0,1\}$ and every $x \in M_i$, the element $L(x)$ lies in $N(M)_i$, the image in $N(M)$ of $M_i\times M_i \subseteq M\times\Sigma$.
--
--   This is the statement that the canonical $L$-map is of degree $0$ for the $\mathbb{Z}/2$-grading, as in the Čerednik–Drinfeld uniformisation theory of Boutot–Carayol, where it follows from $F$ and $\lambda$ both having degree $1$. It is used in the degree bookkeeping that places transported $\eta$-sections in the correct graded piece, via [`CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_mem_etaPiece_add_eq`](thm.html#CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_mem_etaPiece_add_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_apply_mem_nPiece.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.apply_mem_nPiece
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) (i : Fin 2) (x : D.M) (hx : x ∈ D.piece i) :
    L x ∈ D.nPiece i := by sorry
