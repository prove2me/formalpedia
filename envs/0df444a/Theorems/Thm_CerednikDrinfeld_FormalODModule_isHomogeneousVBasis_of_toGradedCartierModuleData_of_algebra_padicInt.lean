-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_toGradedCartierModuleData_of_algebra_padicInt
-- name    : CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_toGradedCartierModuleData_of_algebra_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/ad3e3b2d-905f-5ee0-ab6b-f8dd12960f74
-- title:
--   Abstract homogeneous V-basis is a law-level V-basis
-- statement:
--   Fix a prime $p$, a commutative ring $B$ carrying a $\mathbb{Z}_p$-algebra structure, and a ring homomorphism $j : W(\mathbb{F}_{p^2}) \to B$, where [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17) denotes $W(\mathbb{F}_{p^2})$. Let $X$ be a `FormalODModule p B`, that is, a $2$-dimensional commutative formal group law $F$ over $B$ together with an action of $W(\mathbb{F}_{p^2})$ by law endomorphisms and an endomorphism $\varpi$ satisfying $\varpi \circ \varpi = [p]$ and $\varpi \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \varpi$ for the Witt Frobenius $\sigma$. Assume the two graded pieces $X.gradedPiece\ j\ 0$ and $X.gradedPiece\ j\ 1$ of the Cartier module $M =$ `CartierModule p X.F` are complementary subgroups (`IsCompl`), where `gradedPiece j n` consists of those $f$ with $\mathrm{act}(\tau(c)) \cdot f = [\,j(\tau(c))^{p^n}\,] f$ for all $c \in \mathbb{F}_{p^2}$, $\tau$ the Teichmüller lift. Let $\gamma : \mathrm{Fin}\,2 \to M$ and assume $\gamma$ is a homogeneous $V$-basis of the graded Cartier module datum `X.toGradedCartierModuleData j hc`: each $\gamma_i$ lies in the $i$-th piece, and every $x \in M$ is written uniquely as $x = \sum_i [c_i]\gamma_i + V y$ with $c \in B^2$, $y \in M$, for $V$ the integral Verschiebung and $[\,\cdot\,]$ the Teichmüller action. The conclusion is that $\gamma$ is a homogeneous $V$-basis in the law-level sense: each $\gamma_i$ lies in $X.gradedPiece\ j\ i$, and the $2 \times 2$ matrix $(\mathrm{tangent}(\gamma_i)_k)$ has invertible determinant in $B$.
--
--   This is the converse direction of the comparison between the abstract axiomatic notion of homogeneous $V$-basis for a graded Cartier module datum and the law-level notion formulated via the tangent matrix of the Cartier module of a special formal $\mathcal{O}_D$-module. It is used where base-change and lifting constructions produce abstract bases whereas the law-level statements about special formal modules consume tangent-matrix bases, for instance in the lattice-comparison results on Cartier quadruples.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_toGradedCartierModuleData_of_algebra_padicInt.lean

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
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_toGradedCartierModuleData_of_algebra_padicInt
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [Algebra (PadicInt p) B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X : CerednikDrinfeld.FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F)
    (hγ : (X.toGradedCartierModuleData j hc).IsHomogeneousVBasis γ) :
    X.IsHomogeneousVBasis j γ := by sorry
