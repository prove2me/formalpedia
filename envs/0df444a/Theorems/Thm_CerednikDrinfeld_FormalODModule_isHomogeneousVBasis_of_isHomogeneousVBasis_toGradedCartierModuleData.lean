-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
-- name    : CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/62394348-5057-5fe6-a7c8-6646bff6089c
-- title:
--   Homogeneous V-bases have unit tangent determinant
-- statement:
--   Let $p$ be a prime, let $S$ be a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure, and let $j$ be a ring homomorphism from $\mathbb{Z}_{p^2}=W(\mathbb{F}_{p^2})$ to $S$. Let $X$ be a formal $\mathcal{O}_D$-module over $S$, that is, a commutative $2$-dimensional formal group law $X.F$ together with an action of $\mathbb{Z}_{p^2}$ by endomorphisms of $X.F$ and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\mathrm{Frob}(a)]\circ\varpi$. Write $M=$ `CartierModule p X.F`, and for $n$ let `X.gradedPiece j n` be the subgroup of those $f\in M$ on which every Teichmüller representative $[c]$, $c\in\mathbb{F}_{p^2}$, acts through the $X$-action as the homothety by $j([c])^{p^n}$. Assume `hc`, that `X.gradedPiece j 0` and `X.gradedPiece j 1` are complementary. Let $\gamma:\{0,1\}\to M$ be a family which is a homogeneous $V$-basis of the associated graded Cartier datum `X.toGradedCartierModuleData j hc`: each $\gamma_i$ lies in the piece of degree $i$, and each $x\in M$ is uniquely of the form $\sum_i [c_i]\cdot\gamma_i + V y$ with $c\in S^{\{0,1\}}$ and $y\in M$. The conclusion is `X.IsHomogeneousVBasis j γ`: each $\gamma_i$ lies in `X.gradedPiece j i` and the determinant of the $2\times 2$ matrix $(\mathrm{tangent}(\gamma_i)_k)_{i,k}$ is a unit in $S$.
--
--   This is the passage from the unique-decomposition formulation of a homogeneous $V$-basis of a graded Cartier datum to the determinantal formulation used for formal $\mathcal{O}_D$-modules, as in the Cartier-theoretic description of special formal modules in the Čerednik–Drinfeld uniformisation. It is invoked throughout the analysis of Cartier quadruples and their rigidifications, where homogeneous $V$-bases serve as coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup
open MvFormalGroup.CartierModule

open scoped PadicInt

theorem CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] [Algebra ℤ_[p] S] (j : Zp2 p →+* S)
    (X : FormalODModule p S) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (γ : Fin 2 → CartierModule p X.F)
    (hγ : (X.toGradedCartierModuleData j hc).IsHomogeneousVBasis γ) :
    X.IsHomogeneousVBasis j γ := by sorry
