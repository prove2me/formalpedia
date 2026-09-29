-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_basis_cartierModule_eq_of_hasStructureConstants_edgeConstants
-- name    : CerednikDrinfeld.FormalODModule.exists_basis_cartierModule_eq_of_hasStructureConstants_edgeConstants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/3748b669-8305-55a3-b7b6-6514d062a730
-- title:
--   Edge-family Cartier module is free of rank 4 on γ, Vγ
-- statement:
--   Let $p$ be a prime and $\kappa$ a perfect field of characteristic $p$, equipped with a ring homomorphism $j$ from $\mathbb Z_{p^2} = W(\mathbb F_{p^2})$ to $\kappa$, and let $\xi,\eta\in\kappa$ satisfy $\xi\eta=0$. Let $X$ be a formal $\mathcal O_D$-module over $\kappa$, that is, a commutative two-dimensional formal group law $F$ over $\kappa$ together with an action of $\mathbb Z_{p^2}$ by endomorphisms of $F$ and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ a = \sigma(a)\circ\varpi$ for $a\in\mathbb Z_{p^2}$, with $\sigma$ the Witt-vector Frobenius. Let $\gamma_0,\gamma_1$ be elements of the Cartier module $M$ of $F$ forming a homogeneous $V$-basis with respect to $j$: $\gamma_i$ lies in the $i$-th graded piece, i.e. the Teichmüller action of each $c\in\mathbb F_{p^2}$ sends $\gamma_i$ to $j([c])^{p^i}\gamma_i$, and the matrix of tangent coordinates of $\gamma_0,\gamma_1$ has invertible determinant. Assume the structure constants of $\gamma$ for $\varpi$ are the edge constants attached to $(\xi,\eta)$: for every $i$ and every $N$ there is $h\in M$ with $\varpi\gamma_i=\sum_{m<N}V^m\bigl(a_{m,i}\,\gamma_{(m+i+1)\bmod 2}\bigr)+V^N h$, where $a_{m,0}$ and $a_{m,1}$ are the branch constants of $\eta$ and of $\xi$ respectively, the branch constants of $x$ being $x^p-x$ for $m=0$, $1$ for $m=1$, $(\text{$(m/2)$-th Witt digit of } x)^{p^{m/2}}$ for even $m\ge 2$, and $0$ for odd $m\ge 3$. Then $M$ admits a basis over $W(\kappa)$ indexed by $\{0,1,2,3\}$ whose members are $\gamma_0$, $\gamma_1$, $V\gamma_0$, $V\gamma_1$, in that order; in particular $M$ is free of rank $4$ on these four elements.
--
--   This is the Cartier–Dieudonné module computation for the edge family of special formal $\mathcal O_D$-modules occurring in the Čerednik–Drinfel'd uniformisation: the relations $\varpi\gamma_0=([\eta^p]-[\eta])\gamma_1+V\gamma_0$, $\varpi\gamma_1=([\xi^p]-[\xi])\gamma_0+V\gamma_1$ forced by the edge constants pin down the module over $W(\kappa)$ exactly. It supplies the freeness statement used to show that such a module has height $4$, and is used again in the rigidification arguments computing determinants and numerical invariants of isogenies between edge-family modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_basis_cartierModule_eq_of_hasStructureConstants_edgeConstants.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

theorem CerednikDrinfeld.FormalODModule.exists_basis_cartierModule_eq_of_hasStructureConstants_edgeConstants
    (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p] [PerfectRing κ p] (j : Zp2 p →+* κ)
    (ξ η : κ) (hξη : ξ * η = 0)
    (X : FormalODModule p κ) (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (ha : X.HasStructureConstants γ (EdgeFamily.edgeConstants p ξ η)) :
    ∃ b : Module.Basis (Fin 4) (WittVector p κ) (CartierModule p X.F),
      b 0 = γ 0 ∧ b 1 = γ 1 ∧ b 2 = verschiebungInt (γ 0) ∧ b 3 = verschiebungInt (γ 1) := by sorry
