-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_hasHeight_four_of_hasStructureConstants_edgeConstants_of_perfectRing
-- name    : CerednikDrinfeld.FormalODModule.hasHeight_four_of_hasStructureConstants_edgeConstants_of_perfectRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/94ab40ca-363e-58e8-8350-779179de3797
-- title:
--   Edge structure constants force height four
-- statement:
--   Let $p$ be a prime and $\kappa$ a perfect field of characteristic $p$, let $j\colon W(\mathbb F_{p^2})\to\kappa$ be a ring homomorphism, and let $\xi,\eta\in\kappa$ satisfy $\xi\eta=0$. Let $X$ be a `FormalODModule` over $\kappa$: a commutative two-dimensional formal group law $F$ over $\kappa$ together with an additive and multiplicative action of $W(\mathbb F_{p^2})$ by endomorphisms of $F$ and an endomorphism $\varpi$ of $F$ with $\varpi\circ\varpi$ the action of $p$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\varpi$ for the Witt-vector Frobenius $\sigma$. Let $\gamma_0,\gamma_1$ be elements of the Cartier module of $F$ forming a homogeneous $V$-basis relative to $j$, i.e. $\gamma_i$ lies in the $i$-th graded piece (the Teichmüller element of each $c\in\mathbb F_{p^2}$ acts on $\gamma_i$ as the homothety by $j(\omega(c))^{p^i}$) and the $2\times2$ matrix of tangent coordinates of the $\gamma_i$ has invertible determinant. Assume $X$ has structure constants the edge constants of $\xi,\eta$: for each $i$ and each $N$, the action of $\varpi$ on $\gamma_i$ equals $\sum_{m<N}V^m\bigl(a_{m,i}\gamma_{(m+i+1)\bmod 2}\bigr)+V^N h$ for some $h$ in the Cartier module, where $a_{m,0}$ and $a_{m,1}$ are the branch constants of $\eta$ and of $\xi$ respectively, namely $x^p-x$ for $m=0$, $1$ for $m=1$, the $(m/2)$-th Witt digit of $x$ raised to the power $p^{m/2}$ for even $m\ge 2$, and $0$ for odd $m\ge 3$. Then $X$ has height $4$, i.e. the series giving the action of $p$ has kernel of degree $p^4$ in the sense of `HasKernelOfDegree`.
--
--   This is the height computation for the special formal $\mathcal O_D$-modules arising in the Čerednik–Drinfeld description of the formal upper half plane, the family being parametrised by edge data $(\xi,\eta)$ with $\xi\eta=0$. It is used to compute the $\kappa$-dimension $p^4$ of the algebra of the kernel of multiplication by $p$ over algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_hasHeight_four_of_hasStructureConstants_edgeConstants_of_perfectRing.lean

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

theorem CerednikDrinfeld.FormalODModule.hasHeight_four_of_hasStructureConstants_edgeConstants_of_perfectRing
    (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p] [PerfectRing κ p] (j : Zp2 p →+* κ)
    (ξ η : κ) (hξη : ξ * η = 0)
    (X : FormalODModule p κ) (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (ha : X.HasStructureConstants γ (EdgeFamily.edgeConstants p ξ η)) :
    X.HasHeight 4 := by sorry
