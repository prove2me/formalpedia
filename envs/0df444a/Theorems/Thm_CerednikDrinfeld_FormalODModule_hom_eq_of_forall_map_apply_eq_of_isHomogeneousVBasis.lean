-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_hom_eq_of_forall_map_apply_eq_of_isHomogeneousVBasis
-- name    : CerednikDrinfeld.FormalODModule.hom_eq_of_forall_map_apply_eq_of_isHomogeneousVBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/e2d90306-57c0-5078-a9f6-0ae7ec0b4625
-- title:
--   Homomorphisms from X.F determined on a homogeneous V-basis
-- statement:
--   Let $p$ be a prime and $B$ a commutative ring of characteristic $p$, and let $j : W(\mathbb{F}_{p^2}) \to B$ be a ring homomorphism, where $\mathbb{Z}_{p^2}$ denotes the Witt vectors of the field with $p^2$ elements. Let $X$ be a formal $\mathcal{O}_D$-module over $B$: a two-dimensional commutative formal group law $X.F$ together with an action of $W(\mathbb{F}_{p^2})$ by endomorphisms of $X.F$ and a uniformiser series $\varpi$ satisfying $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\sigma(a)] \circ \varpi$ for the Frobenius $\sigma$. Let $G$ be a commutative formal group law over $B$ of dimension $d'$, and let $\gamma_0,\gamma_1$ be elements of the Cartier module of curves of $X.F$ at $p$ forming a homogeneous $V$-basis in the sense of the project: each $\gamma_i$ lies in the $i$-th graded piece for $j$, meaning that the action of the Teichmüller lift of every $c \in \mathbb{F}_{p^2}$ on $\gamma_i$ equals the homothety by $j(\tau(c))^{p^i}$, and the determinant of the $2 \times 2$ matrix of tangent coefficients $(\mathrm{tangent}(\gamma_i)_k)$ is a unit in $B$. If two homomorphisms $\varphi, \psi : X.F \to G$ of formal group laws induce the same map on Cartier modules at $\gamma_0$ and $\gamma_1$, then $\varphi = \psi$. The proof uses only the invertibility of the tangent determinant, not the homogeneity of the $\gamma_i$.
--
--   This is the rigidity statement of Cartier–Dieudonné theory in characteristic $p$ used in the Čerednik–Drinfel'd setting: a homomorphism out of the formal group law of a special formal $\mathcal{O}_D$-module is determined by its effect on a $V$-basis of the associated module of curves. It is invoked in the study of Cartier quadruples for rigidified special formal modules, in particular in the isomorphism criterion obtained by transporting a line in the non-nodal case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_hom_eq_of_forall_map_apply_eq_of_isHomogeneousVBasis.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

theorem CerednikDrinfeld.FormalODModule.hom_eq_of_forall_map_apply_eq_of_isHomogeneousVBasis
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X : CerednikDrinfeld.FormalODModule p B) {d' : ℕ} (G : MvFormalGroup d' B) [G.IsComm]
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (φ ψ : MvFormalGroup.Hom X.F G)
    (h : ∀ i : Fin 2, MvFormalGroup.CartierModule.map φ (γ i) = MvFormalGroup.CartierModule.map ψ (γ i)) :
    φ = ψ := by sorry
