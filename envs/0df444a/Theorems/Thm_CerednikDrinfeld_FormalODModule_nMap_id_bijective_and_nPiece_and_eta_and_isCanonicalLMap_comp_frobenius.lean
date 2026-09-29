-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_nMap_id_bijective_and_nPiece_and_eta_and_isCanonicalLMap_comp_frobenius
-- name    : CerednikDrinfeld.FormalODModule.nMap_id_bijective_and_nPiece_and_eta_and_isCanonicalLMap_comp_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/16adc805-8b88-53a2-bf14-6304e540d465
-- title:
--   Frobenius twist of the labelling: N, pieces, η, canonicity
-- statement:
--   Let $p$ be a prime, $C$ a commutative ring, and $X$ a formal $\mathcal O_D$-module over $C$: a commutative two-dimensional formal group law $F$ with an additive, multiplicative action of $\mathbb Z_{p^2}=W(\mathbb F_{p^2})$ and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ a=\sigma(a)\circ\varpi$. Let $j\colon\mathbb Z_{p^2}\to C$ be a ring homomorphism, let $M=\mathrm{CartierModule}\,p\,F$, and for $n$ let $M^j_n$ be the subgroup of those $f$ on which the action of the Teichmüller lift of each $c\in\mathbb F_{p^2}$ agrees with the homothety by $j(\mathrm{teich}(c))^{p^n}$. Assume $M^j_0,M^j_1$ are complementary, and likewise $M^{j\sigma}_0,M^{j\sigma}_1$ for $j\circ\sigma$, $\sigma$ the Witt-vector Frobenius of $\mathbb Z_{p^2}$; this yields graded Cartier data $D$ and $D'$ sharing $M$, the Frobenius, the integral Verschiebung $V$ and $\varpi$, with pieces $M^j_i$ respectively $M^{j\sigma}_i$. Let $I\colon N(D)\to N(D')$ be an additive map with $I(\mathrm{nMk}(x,y))=\mathrm{nMk}'(x,y)$ for all $x,y\in M$, where $N(\cdot)$ is the quotient of $M\times M^{(\sigma)}$ by the standard relation submodule and $\mathrm{nMk}$ the induced map from $M\times M$. Then: (i) $I$ is bijective; (ii) $I$ intertwines the operators $\varpi$ on $N(D)$ and $N(D')$; (iii) for each $i\in\mathrm{Fin}\,2$ and $z\in N(D)$, $z$ lies in $\mathrm{nMk}(M^j_i\times M^j_i)$ if and only if $Iz$ lies in $\mathrm{nMk}'(M^{j\sigma}_{i+1}\times M^{j\sigma}_{i+1})$; and (iv) for every additive $L\colon M\to N(D)$ which is a Cartier $L$-map for $D$ (i.e. $L(w\cdot x)=\sigma(w)\cdot L(x)$, $L(Vx)=\mathrm{nMk}(\varpi x,0)$, and $\lambda\circ L$ equals the Frobenius of $M$), the composite $I\circ L$ is a Cartier $L$-map for $D'$, and moreover for this witness: for each $i$ and $z$, $z$ lies in $\mathrm{eta}(L)\cap\mathrm{nPiece}_i$ for $D$ if and only if $Iz$ lies in $\mathrm{eta}(I\circ L)\cap\mathrm{nPiece}_{i+1}$ for $D'$, and $L$ is a canonical $L$-map for $D$ (a Cartier $L$-map admitting a lift through a base change along a surjection onto $C$ from a ring without $p$-torsion in the stated sense, from a Cartier $L$-map on a special graded Cartier datum there) if and only if $I\circ L$ is a canonical $L$-map for $D'$.
--
--   This is the bookkeeping for an odd Frobenius twist of the labelling $j$: the module $N$, the map $\lambda$, the operator $\varpi$ and the subgroup $\eta$ attached to an $L$-map are insensitive to the grading, while the two-step grading shifts by one because $M^{j\sigma}_n=M^j_{n+1}$, and canonicity is preserved by twisting the labelling of the lifting datum as well. It is used in the description of the Cartier quadruple attached to an odd lattice translate and in the corresponding statement about $\eta$-sections under the $GL_2(\mathbb Q_p)$-action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_nMap_id_bijective_and_nPiece_and_eta_and_isCanonicalLMap_comp_frobenius.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_ODModuleFrobeniusTwist

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.FormalODModule.nMap_id_bijective_and_nPiece_and_eta_and_isCanonicalLMap_comp_frobenius
    (p : ℕ) [Fact p.Prime] {C : Type} [CommRing C] (X : FormalODModule p C) (j : Zp2 p →+* C)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (hc' : IsCompl (X.gradedPiece (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) 0)
      (X.gradedPiece (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) 1))
    (I : (X.toGradedCartierModuleData j hc).NMod →+ (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').NMod)
    (hI : ∀ x y : MvFormalGroup.CartierModule p X.F, I ((X.toGradedCartierModuleData j hc).nMk (x, y)) = (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').nMk (x, y)) :
    Function.Bijective I ∧
    (∀ z, I ((X.toGradedCartierModuleData j hc).nVarpi z) = (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').nVarpi (I z)) ∧
    (∀ (i : Fin 2) (z : (X.toGradedCartierModuleData j hc).NMod), z ∈ (X.toGradedCartierModuleData j hc).nPiece i ↔ I z ∈ (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').nPiece (i + 1)) ∧
    (∀ (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod) (hL : (X.toGradedCartierModuleData j hc).IsCartierLMap L),
      ∃ hL' : (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').IsCartierLMap (I.comp L),
        (∀ (i : Fin 2) (z : (X.toGradedCartierModuleData j hc).NMod), z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.map_verschiebung i ↔
          I z ∈ (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').etaPiece (I.comp L) hL'.map_verschiebung (i + 1)) ∧
        ((X.toGradedCartierModuleData j hc).IsCanonicalLMap L ↔ (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').IsCanonicalLMap (I.comp L))) := by sorry
