-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_IsHomogeneousVBasis_tangent_mem_and_existsUnique_smul_of_isNilpotent
-- name    : CerednikDrinfeld.FormalODModule.IsHomogeneousVBasis.tangent_mem_and_existsUnique_smul_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/97a39a47-ca67-54be-92de-0418f903c360
-- title:
--   Tangent vectors of a homogeneous V-basis grade LieX
-- statement:
--   Fix a prime $p$, a commutative ring $B$, a ring homomorphism $j \colon W(\mathbb{F}_{p^2}) \to B$ (the ring [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17) being the Witt vectors of $\mathrm{GF}(p,2)$), and assume $p$ is nilpotent in $B$. Let $X$ be a formal $\mathcal{O}_D$-module over $B$, that is, a commutative $2$-dimensional formal group law $F$ over $B$ together with an action of $W(\mathbb{F}_{p^2})$ by law endomorphisms and a law endomorphism $\varpi$ with $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$. Let $\gamma_0,\gamma_1$ be elements of the Cartier module of $F$ forming a homogeneous $V$-basis with respect to $j$: each $\gamma_i$ lies in the $i$-th graded piece, i.e. for every $c \in \mathrm{GF}(p,2)$ the operator induced by the action of the Teichmüller lift of $c$ sends $\gamma_i$ to the homothety by $j(\text{teichmüller } c)^{p^i}$ of $\gamma_i$; and the $2 \times 2$ matrix whose $(i,k)$ entry is the $k$-th coordinate of the tangent vector $t(\gamma_i)$ has unit determinant. Here $t$ is the additive tangent map sending a curve to the coefficients of its linear term. Write $\mathrm{Lie}(X)_0$ for the submodule $\bigcap_{a} \ker(\mathrm{lieAct}(a) - j(a)\,\mathrm{id})$ of $\mathrm{Lie}(X)$ and $\mathrm{Lie}(X)_1$ for $\bigcap_a \ker(\mathrm{lieAct}(a) - j(\sigma a)\,\mathrm{id})$, where $\mathrm{lieAct}(a)$ is multiplication by the linear part of the law endomorphism $[a]$. The conclusion is fourfold: $t(\gamma_0) \in \mathrm{Lie}(X)_0$ and $t(\gamma_1) \in \mathrm{Lie}(X)_1$; every $v \in \mathrm{Lie}(X)_0$ is $b \cdot t(\gamma_0)$ for a unique $b \in B$; every $v \in \mathrm{Lie}(X)_1$ is $b \cdot t(\gamma_1)$ for a unique $b \in B$; and $\mathrm{Lie}(X)_0$, $\mathrm{Lie}(X)_1$ are complementary submodules of $\mathrm{Lie}(X)$.
--
--   This is the statement that the tangent vectors of a homogeneous $V$-basis of the Cartier module of a special formal $\mathcal{O}_D$-module form a basis adapted to the eigenspace decomposition $\mathrm{Lie}(X) = \mathrm{Lie}(X)_0 \oplus \mathrm{Lie}(X)_1$ for the $W(\mathbb{F}_{p^2})$-action, as in the Čerednik–Drinfeld uniformisation theory of Boutot–Carayol. It supplies the coordinates in which later results compute $\eta$-sections and the tangent data attached to edges and nodes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_IsHomogeneousVBasis_tangent_mem_and_existsUnique_smul_of_isNilpotent.lean

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

theorem CerednikDrinfeld.FormalODModule.IsHomogeneousVBasis.tangent_mem_and_existsUnique_smul_of_isNilpotent
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B) (hB : IsNilpotent (p : B))
    (X : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ) :
    (MvFormalGroup.CartierModule.tangent (γ 0) ∈ X.lieZero j ∧
      MvFormalGroup.CartierModule.tangent (γ 1) ∈ X.lieOne j) ∧
    (∀ v ∈ X.lieZero j, ∃! b : B, v = b • MvFormalGroup.CartierModule.tangent (γ 0)) ∧
    (∀ v ∈ X.lieOne j, ∃! b : B, v = b • MvFormalGroup.CartierModule.tangent (γ 1)) ∧
    IsCompl (X.lieZero j) (X.lieOne j) := by sorry
