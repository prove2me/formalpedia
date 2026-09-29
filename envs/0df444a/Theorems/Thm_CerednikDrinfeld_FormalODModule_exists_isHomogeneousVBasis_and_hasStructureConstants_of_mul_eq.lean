-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq
-- name    : CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/02d71359-c512-5e7d-b17b-466cdf9b5437
-- title:
--   Prescribed structure constants are realised by a formal mathcal O_D-module
-- statement:
--   Let $p$ be a prime, let $B$ be a commutative ring, let $j \colon \mathbb Z_{p^2} = W(\mathbb F_{p^2}) \to B$ be a ring homomorphism, and let $a \colon \mathbb N \to \mathrm{Fin}\,2 \to B$ be a family of elements of $B$ subject to the single relation $a_{0,0}\,a_{0,1} = p$ in $B$. Then there exist a [`CerednikDrinfeld.FormalODModule p B`](def/CerednikDrinfeld_SpecialFormalModule.html#L170), that is a two-dimensional commutative formal group law $F$ over $B$ together with an action $\mathbb Z_{p^2} \to$ (law endomorphisms of $F$) which is unital, multiplicative for composition and additive for $F$, and a further endomorphism $\varpi$ with $\varpi \circ \varpi$ the action of $p$ and $\varpi \circ [\alpha] = [\sigma(\alpha)] \circ \varpi$ for the Witt-vector Frobenius $\sigma$; and a pair $\gamma_0, \gamma_1$ of elements of the Cartier module of $F$, such that: (i) for each $i$ and each $c \in \mathbb F_{p^2}$ the Teichmüller element $[c]$ acts on $\gamma_i$ as the homothety by $j([c])^{p^i}$, and the $2 \times 2$ matrix of tangent vectors of $\gamma_0, \gamma_1$ has determinant a unit; and (ii) for every $i$ and every $N$ there is an element $h$ of the Cartier module with $\varpi_*\gamma_i = \sum_{m<N} V^m\langle a_{m,i}\rangle \gamma_{(m+i+1) \bmod 2} + V^N h$, where $V$ is the Verschiebung and $\langle b \rangle$ the homothety by $b$.
--
--   This is the surjectivity half of the Cartier-theoretic description of Drinfeld's special formal $\mathcal O_D$-modules: any datum of structure constants constrained only by $a_{0,0}a_{0,1}=p$ — the two coordinates of the local model $W[[u,v]]/(uv-p)$ — is realised by an actual formal $\mathcal O_D$-module law with a homogeneous $V$-basis over an arbitrary $\mathbb Z_{p^2}$-algebra $B$. It is the existence input for the later classification statements over algebraically closed fields, over lift rings and up to isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (a : ℕ → Fin 2 → B) (ha : a 0 0 * a 0 1 = (p : B)) :
    ∃ (X : CerednikDrinfeld.FormalODModule p B)
      (γ : Fin 2 → MvFormalGroup.CartierModule p X.F),
      X.IsHomogeneousVBasis j γ ∧ X.HasStructureConstants γ a := by sorry
