-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_of_free
-- name    : CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_of_free
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/2440ae8d-7b6e-5f92-a99b-09726a842cc7
-- title:
--   Homogeneous V-basis for a special formal mathcal O_D-module with free Lie lines
-- statement:
--   Let $p$ be a prime and $B$ a commutative ring of characteristic $p$, let $j\colon W(\mathbb F_{p^2})\to B$ be a ring homomorphism (the source being [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17), the Witt vectors of `GaloisField p 2`), and let $X$ be a formal $\mathcal O_D$-module over $B$: a commutative $2$-dimensional formal group law $F$ together with an action of $W(\mathbb F_{p^2})$ and an endomorphism $\varpi$ by law homomorphisms of $F$, satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$ for the Witt Frobenius $\sigma$. Assume $X$ is special for $j$, i.e. the submodules $\mathrm{lieZero}$ and $\mathrm{lieOne}$ of $\operatorname{Lie}X$ — the intersections over $a$ of the kernels of $\mathrm{lieAct}\,a - j(a)$, respectively $\mathrm{lieAct}\,a - j(\sigma a)$, where $\mathrm{lieAct}\,a$ is multiplication by the linear part of the action of $a$ — are complementary and both invertible as $B$-modules, and assume in addition that both are free $B$-modules. Then there exists a pair $\gamma\colon\mathrm{Fin}\,2\to$ `CartierModule p X.F` which is a homogeneous $V$-basis for $j$: each $\gamma_i$ lies in the graded piece of index $i$, consisting of those $f$ with $[\,c\,]$ acting on $f$ as the homothety by $j([c])^{p^i}$ for every $c\in\mathbb F_{p^2}$, and the $2\times 2$ matrix $(i,k)\mapsto \mathrm{tangent}(\gamma_i)_k$ has invertible determinant.
--
--   This is the existence of a homogeneous $V$-basis $(\gamma_0,\gamma_1)$ of the Cartier module of a special formal $\mathcal O_D$-module, the starting point of Boutot–Carayol's analysis of special graded Cartier modules and of the graded $V$-adic expansions used in the study of Drinfeld's functors. It is invoked in the construction of canonical linear maps to graded Cartier module data, in the variant over a field, and in the treatment of the quotient of the Witt vector module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_of_free.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_of_free
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [CharP B p]
    (j : CerednikDrinfeld.Zp2 p →+* B) (X : CerednikDrinfeld.FormalODModule p B)
    (hX : X.IsSpecial j) (h₀ : Module.Free B ↥(X.lieZero j)) (h₁ : Module.Free B ↥(X.lieOne j)) :
    ∃ γ : Fin 2 → MvFormalGroup.CartierModule p X.F, X.IsHomogeneousVBasis j γ := by sorry
