-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis
-- name    : CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/f630f70f-0b9b-5f8a-846e-d3f6d27f232f
-- title:
--   Homogeneous V-basis splits the Cartier module into graded pieces
-- statement:
--   Fix a prime $p$, a commutative ring $B$, and a ring homomorphism $j \colon W(\mathbb F_{p^2}) \to B$ from the Witt vectors of the field with $p^2$ elements (written `Zp2 p`). Let $X$ be a formal $\mathcal O_D$-module over $B$: a two-dimensional commutative formal group law $X.F$ over $B$ together with an action of $W(\mathbb F_{p^2})$ by endomorphism series and a series $\varpi$, with $\varpi \circ \varpi$ equal to the action of $p$ and $\varpi \circ [a] = [\sigma(a)] \circ \varpi$ for the Witt Frobenius $\sigma$. For $n \in \mathbb N$, the graded piece `X.gradedPiece j n` is the additive subgroup of the Cartier module $\mathrm{CartierModule}(p, X.F)$ consisting of those $f$ with $[\tau(c)] \cdot f = j(\tau(c))^{p^n} f$ (action of the endomorphism induced by the Teichmüller lift $\tau(c)$ on the left, homothety on the right) for every $c \in \mathbb F_{p^2}$. Let $\gamma_0,\gamma_1$ be elements of the Cartier module forming a homogeneous $V$-basis with respect to $j$, i.e. $\gamma_i$ lies in `X.gradedPiece j i` for $i = 0,1$ and the determinant of the $2 \times 2$ matrix of tangent coordinates $\mathrm{tangent}(\gamma_i)_k$ is a unit of $B$. The conclusion is that `X.gradedPiece j 0` and `X.gradedPiece j 1` are complementary additive subgroups of the Cartier module: their intersection is zero and together they generate the whole module.
--
--   This is the splitting of the Cartier module of a special formal module into the two eigencomponents for the action of the unramified quadratic subring $W(\mathbb F_{p^2})$, in the form used for Drinfeld's description of special formal $\mathcal O_D$-modules; no nilpotency hypothesis on $B$ is imposed. It is used in the construction of bases adapted to the grading, in the passage from a formal $\mathcal O_D$-module to graded Cartier module data, and in the converse construction of a formal $\mathcal O_D$-module from such data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis.lean

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

theorem CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isHomogeneousVBasis
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ) :
    IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1) := by sorry
