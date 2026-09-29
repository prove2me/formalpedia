-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
-- name    : CerednikDrinfeld.FormalODModule.isBaseChangeAlong_toGradedCartierModuleData_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/e8ca7dee-b363-5b8c-a531-74b84f83b174
-- title:
--   Base change of the graded Cartier datum of X
-- statement:
--   Fix a prime $p$, commutative rings $B$ and $S$, a ring homomorphism $j \colon W(\mathbb{F}_{p^2}) \to B$, a ring homomorphism $g \colon B \to S$, and a formal $\mathcal{O}_D$-module $X$ over $B$, that is, a two-dimensional commutative formal group law $X.F$ over $B$ together with an action of $W(\mathbb{F}_{p^2})$ by endomorphisms of $X.F$ and an endomorphism $\varpi$ with $\varpi \circ \varpi$ the action of $p$ and $\varpi \circ a = \mathrm{Frob}(a) \circ \varpi$. Let $\gamma \colon \mathrm{Fin}\,2 \to \mathrm{CartierModule}\,p\,X.F$ satisfy `X.IsHomogeneousVBasis j γ`: each $\gamma i$ lies in the graded piece `X.gradedPiece j i`, consisting of those $f$ with $\mathrm{endAct}(X.\mathrm{actEnd}(\tau c))\,f = \mathrm{homothety}(j(\tau c)^{p^i})\,f$ for every $c \in \mathbb{F}_{p^2}$ (with $\tau$ the Teichmüller lift), and the determinant of the $2 \times 2$ tangent matrix $(\mathrm{tangent}(\gamma i)\,k)_{i,k}$ is a unit. Assume further that the pieces of degrees $0$ and $1$ are complementary submodules, both for $X$ with $j$ over $B$ and for the coefficientwise base change $X.\mathrm{map}\,g$ with $g \circ j$ over $S$. Then the additive map $\mathrm{baseChange}\,g \colon \mathrm{CartierModule}\,p\,X.F \to \mathrm{CartierModule}\,p\,(X.F.\mathrm{map}\,g)$ exhibits the graded Cartier module datum of $X.\mathrm{map}\,g$ as a base change along $g$ of that of $X$: it is semilinear for $W(g)$ on Witt scalars, commutes with the Frobenius, with the integral Verschiebung and with the operator induced by $\varpi$, sends the piece of degree $i$ into the piece of degree $i$, and there is a family in the source which is a homogeneous $V$-basis in the abstract sense (lying degreewise in the pieces, and such that every element has a unique expression $\sum_i \tau(c_i)\gamma_i + V y$) and whose image is again such a basis downstairs.
--
--   This is the naturality in the base ring of the Cartier-theoretic description of special formal $\mathcal{O}_D$-modules: the Cartier module datum attached to $X \otimes_B S$ is the base change of the datum attached to $X$. It is used for the naturality of the Cartier quadruple and of the canonical $L$-map attached to a formal $\mathcal{O}_D$-module, and is invoked by the lemmas on torsion-freeness and on the existence of canonical $L$-maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.isBaseChangeAlong_toGradedCartierModuleData_baseChange
    (p : ℕ) [Fact p.Prime] {B S : Type} [CommRing B] [CommRing S] (j : CerednikDrinfeld.Zp2 p →+* B)
    (g : B →+* S) (X : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (hc' : IsCompl ((X.map g).gradedPiece (g.comp j) 0) ((X.map g).gradedPiece (g.comp j) 1)) :
    CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong g
      (X.toGradedCartierModuleData j hc) ((X.map g).toGradedCartierModuleData (g.comp j) hc')
      (MvFormalGroup.CartierModule.baseChange (Φ := X.F) g) := by sorry
