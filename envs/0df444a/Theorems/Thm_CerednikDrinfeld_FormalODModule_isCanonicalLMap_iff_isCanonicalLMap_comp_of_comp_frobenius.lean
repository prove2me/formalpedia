-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_iff_isCanonicalLMap_comp_of_comp_frobenius
-- name    : CerednikDrinfeld.FormalODModule.isCanonicalLMap_iff_isCanonicalLMap_comp_of_comp_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/a0b0e895-7fb1-53b9-b87e-018e2536cf2d
-- title:
--   Canonicity of L-maps under the σ-shift of the grading
-- statement:
--   Let $p$ be a prime, $C$ a commutative ring and $X$ a formal $\mathcal O_D$-module over $C$ (a two-dimensional commutative formal group law $F$ over $C$ together with series giving an action of $\mathbb Z_{p^2}=W(\mathbb F_{p^2})$ and a series $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$), and let $j\colon \mathbb Z_{p^2}\to C$ be a ring homomorphism. Write $\sigma$ for `WittVector.frobenius` on $\mathbb Z_{p^2}$. For $n$, the $n$-th graded piece is the subgroup of the Cartier module of $F$ consisting of those $f$ with $[\omega(c)]_*f=j(\omega(c))^{p^n}f$ for every $c\in\mathbb F_{p^2}$, $\omega$ the Teichmüller lift. Assume the pieces $0$ and $1$ are complementary both for $j$ (hypothesis `hc`) and for $j\circ\sigma$ (hypothesis `hc'`), and let $D$, $D'$ be the resulting graded Cartier module data, with underlying module the Cartier module of $F$, Frobenius and Verschiebung the usual operators, $\varpi$ acting through `varpiEnd`, and pieces indexed by `Fin 2`. Let $I\colon N(D)\to N(D')$ be an additive map which is the identity on classes, i.e. $I(\mathrm{nMk}_D(x,y))=\mathrm{nMk}_{D'}(x,y)$ for all $x,y$. Let $L\colon D.M\to N(D)$ be an additive map which is a Cartier $L$-map for $D$ ($\sigma$-semilinear, $L(Vx)=\mathrm{nMk}(\varpi x,0)$, and $\lambda\circ L=F$), and assume $I\circ L$ is a Cartier $L$-map for $D'$. Then $L$ is a canonical $L$-map for $D$ if and only if $I\circ L$ is a canonical $L$-map for $D'$; canonicity means, besides being a Cartier $L$-map, that the map is the push-forward along a base change of a Cartier $L$-map of a special graded Cartier module datum over some $p$-torsion-free ring $S$ with a labelling $\mathbb Z_{p^2}\to S$ and a surjection $S\to C$.
--
--   This is the canonicity clause of the transport of $L$-maps under relabelling the $\mathbb Z_{p^2}$-grading by the Frobenius $\sigma$, in the Cartier-module description of formal $\mathcal O_D$-modules used in the Čerednik–Drinfeld uniformisation. It feeds into [`CerednikDrinfeld.FormalODModule.nMap_id_bijective_and_nPiece_and_eta_and_isCanonicalLMap_comp_frobenius`](thm.html#CerednikDrinfeld.FormalODModule.nMap_id_bijective_and_nPiece_and_eta_and_isCanonicalLMap_comp_frobenius), where the $\sigma$-shift is assembled for odd-parity translates of the Cartier data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_iff_isCanonicalLMap_comp_of_comp_frobenius.lean

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

theorem CerednikDrinfeld.FormalODModule.isCanonicalLMap_iff_isCanonicalLMap_comp_of_comp_frobenius
    (p : ℕ) [Fact p.Prime] {C : Type} [CommRing C] (X : FormalODModule p C) (j : Zp2 p →+* C)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (hc' : IsCompl (X.gradedPiece (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) 0)
      (X.gradedPiece (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) 1))
    (I : (X.toGradedCartierModuleData j hc).NMod →+ (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').NMod)
    (hI : ∀ x y : MvFormalGroup.CartierModule p X.F, I ((X.toGradedCartierModuleData j hc).nMk (x, y)) = (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').nMk (x, y))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod) (hL : (X.toGradedCartierModuleData j hc).IsCartierLMap L) (hL' : (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').IsCartierLMap (I.comp L)) :
    (X.toGradedCartierModuleData j hc).IsCanonicalLMap L ↔ (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').IsCanonicalLMap (I.comp L) := by sorry
