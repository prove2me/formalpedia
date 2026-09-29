-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_field
-- name    : CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/18163ec6-dfbf-589c-bc53-df9b84087329
-- title:
--   Homogeneous V-basis for special formal mathcal O_D-modules over a field
-- statement:
--   Fix a prime $p$ and a field $K$ of characteristic $p$, together with a ring homomorphism $j$ from $\mathbb{Z}_{p^2}=$ [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17) (the Witt vectors of the field with $p^2$ elements) to $K$, and let $X$ be a formal $\mathcal O_D$-module over $K$ in the sense of [`CerednikDrinfeld.FormalODModule`](def/CerednikDrinfeld_SpecialFormalModule.html#L170): a two-dimensional commutative formal group law $X.F$ over $K$, an action of $\mathbb{Z}_{p^2}$ by endomorphisms of $X.F$ which is multiplicative and additive for the group law and sends $1$ to the identity, and an endomorphism $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma(a)]\circ\varpi$ for the Witt Frobenius $\sigma$. Assume $X$ is special relative to $j$, i.e. the two submodules of $\operatorname{Lie}X$ on which every $a\in\mathbb{Z}_{p^2}$ acts by $j(a)$, respectively by $j(\sigma(a))$, are complementary and each invertible as a $K$-module. The conclusion asserts the existence of two elements $\gamma_0,\gamma_1$ of the Cartier module $\operatorname{CartierModule}(p,X.F)$ forming a homogeneous $V$-basis: $\gamma_i$ lies in the graded piece of index $i$, i.e. the Teichmüller endomorphism attached to each $c\in\mathbb{F}_{p^2}$ acts on $\gamma_i$ as the homothety by $j(\tau(c))^{p^i}$, and the $2\times2$ matrix of tangent coordinates $(\operatorname{tangent}(\gamma_i)_k)$ has invertible determinant.
--
--   This is the rigidification step for special formal $\mathcal O_D$-modules in the Čerednik–Drinfel'd setting: over a field of characteristic $p$ a special module admits a basis of its Cartier module adapted to the $\mathbb{Z}_{p^2}$-grading, which is what makes the explicit $2\times2$ matrix description of such modules available. It is used downstream in the analysis of critical charts, in the comparison of invariants after base change to an algebraically closed field, and in the length computation for the graded quotient by $\varpi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_field.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_field
    (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [CharP K p] (j : CerednikDrinfeld.Zp2 p →+* K)
    (X : CerednikDrinfeld.FormalODModule p K) (hX : X.IsSpecial j) :
    ∃ γ : Fin 2 → MvFormalGroup.CartierModule p X.F, X.IsHomogeneousVBasis j γ := by sorry
