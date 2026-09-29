-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants
-- name    : CerednikDrinfeld.FormalODModule.linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/a39434cc-767a-5cc5-a324-1ba4e07bdf76
-- title:
--   Order-zero structure constants give the tangent action of varpi
-- statement:
--   Let $p$ be a prime, $B$ a commutative ring, and let $X$ be a formal $\mathcal O_D$-module over $B$ in the sense of the project's structure [`CerednikDrinfeld.FormalODModule`](def/CerednikDrinfeld_SpecialFormalModule.html#L170): a two-dimensional formal group law $X.F$ over $B$ which is commutative, together with a family of endomorphism series `act` indexed by `Zp2 p` and a series $X.\mathtt{varpi}$, all of them law homomorphisms $X.F \to X.F$, subject to the usual multiplicativity and additivity relations for `act`, to $\mathtt{varpi} \circ \mathtt{varpi} = \mathtt{act}(p)$, and to $\mathtt{varpi} \circ \mathtt{act}(a) = \mathtt{act}(\varphi(a)) \circ \mathtt{varpi}$ for the Witt-vector Frobenius $\varphi$. Let $\gamma_0,\gamma_1$ be elements of the Cartier module $\mathtt{CartierModule}\,p\,X.F$, and let $a : \mathbb N \to \mathrm{Fin}\,2 \to B$ satisfy `X.HasStructureConstants γ a`, that is: for every index $i$ and every $N$ there is a Cartier module element $h$ with $$\varpi\cdot\gamma_i = \sum_{m<N} V^m\bigl(\langle a_{m,i}\rangle\gamma_{\pi(m,i)}\bigr) + V^N h,$$ where $V$ is `verschiebungInt`, $\langle\,\cdot\,\rangle$ is `homothety`, $\varpi$ acts through `X.varpiEnd`, and $\pi(m,i) = (m+i+1) \bmod 2$. Then for each $i$ the matrix $\mathtt{linearPart}\,X.\mathtt{varpi}$, whose $(i,j)$ entry is the coefficient of $X_j$ in the $i$-th component of $\mathtt{varpi}$, satisfies $$\mathtt{linearPart}\,X.\mathtt{varpi} \cdot \mathtt{tangent}(\gamma_i) = a_{0,i}\,\mathtt{tangent}(\gamma_{\pi(0,i)}),$$ where $\mathtt{tangent}$ sends a Cartier module element to the vector of coefficients of the first variable in degree one, and $\pi(0,i) = (i+1)\bmod 2$.
--
--   This identifies the action of $\varpi$ on the tangent space (Lie algebra) of $X$ in terms of the order-zero structure constants of $\gamma$: in the basis $(\mathtt{tangent}\,\gamma_0, \mathtt{tangent}\,\gamma_1)$ the matrix of $\varpi$ is off-diagonal with entries $a_{0,0}, a_{0,1}$. It is used in the analysis of Cartier quadruples and $\eta$-sections attached to special formal modules, where the pair $(a_{0,0},a_{0,1})$ supplies the Lie coordinates of the deformation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants.lean

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

open scoped Matrix in

theorem CerednikDrinfeld.FormalODModule.linearPart_varpi_mulVec_tangent_eq_smul_of_hasStructureConstants
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (X : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (a : ℕ → Fin 2 → B)
    (ha : X.HasStructureConstants γ a) (i : Fin 2) :
    MvFormalGroup.linearPart X.varpi *ᵥ MvFormalGroup.CartierModule.tangent (γ i) =
      a 0 i • MvFormalGroup.CartierModule.tangent (γ (CerednikDrinfeld.FormalODModule.piIndex 0 i)) := by sorry
