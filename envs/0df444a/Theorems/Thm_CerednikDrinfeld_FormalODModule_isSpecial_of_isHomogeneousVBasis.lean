-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecial_of_isHomogeneousVBasis
-- name    : CerednikDrinfeld.FormalODModule.isSpecial_of_isHomogeneousVBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/9523e4b4-9c3f-581f-8e8d-06067c38801e
-- title:
--   Homogeneous V-basis implies the formal mathcal O_D-module is special
-- statement:
--   Let $p$ be a prime, $B$ a commutative ring, and $j \colon \mathbb Z_{p^2} = W(\mathbb F_{p^2}) \to B$ a ring homomorphism, and assume $B$ is Hausdorff for the filtration by the powers of the ideal $(p)$. Let $X$ be a formal $\mathcal O_D$-module over $B$: a commutative $2$-dimensional formal group law $X.F$ over $B$ together with power-series endomorphisms $\mathrm{act}(a)$ for $a \in \mathbb Z_{p^2}$ and an endomorphism $\varpi$, the former forming a ring action ($\mathrm{act}(1) = \mathrm{id}$, multiplicativity under composition, additivity via the group law) and the latter satisfying $\varpi \circ \varpi = \mathrm{act}(p)$ and $\varpi \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \varpi$ with $\sigma$ the Witt-vector Frobenius. Let $\gamma_0, \gamma_1$ be elements of the Cartier module of $X.F$ forming a homogeneous $V$-basis for $j$, that is: for each $i \in \{0,1\}$ and each $c \in \mathbb F_{p^2}$ the endomorphism induced by $\mathrm{act}$ of the Teichmüller lift of $c$ sends $\gamma_i$ to the homothety by $j(\tau(c))^{p^i}$ applied to $\gamma_i$, and the $2 \times 2$ matrix of tangent vectors $\bigl(\mathrm{tangent}(\gamma_i)_k\bigr)_{i,k}$ has determinant a unit of $B$. The conclusion is that $X$ is special for $j$: the two $B$-submodules of $\operatorname{Lie} X$ given by $\bigcap_{a \in \mathbb Z_{p^2}} \ker(\mathrm{lieAct}(a) - j(a)\,\mathrm{id})$ and $\bigcap_{a \in \mathbb Z_{p^2}} \ker(\mathrm{lieAct}(a) - j(\sigma a)\,\mathrm{id})$ are complementary in $\operatorname{Lie} X$, and each of them is an invertible $B$-module.
--
--   This is the implication "$M$ special $\Rightarrow$ $X$ special" in the Cartier-module description of special formal $\mathcal O_D$-modules of Boutot–Carayol II §2: the grading on the Lie algebra and the grading on the Cartier module are both given by the $\mathbb Z_{p^2}$-action, so a homogeneous $V$-basis produces the required decomposition of $\operatorname{Lie} X$ into two invertible pieces. It is used in the Čerednik–Drinfeld part of the formalisation, in particular in the construction of special formal $\mathcal O_D$-modules with prescribed structure constants over algebraically closed fields and in the analysis of admissible Cartier quadruples.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isSpecial_of_isHomogeneousVBasis.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.isSpecial_of_isHomogeneousVBasis
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hsep : IsHausdorff (Ideal.span {(p : B)}) B)
    (X : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ) :
    X.IsSpecial j := by sorry
