-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso
-- name    : CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/f3c1290e-1fe9-55f6-a11c-5fbf3a522d63
-- title:
--   Transport of homogeneous V-bases and structure constants along an isomorphism
-- statement:
--   Fix a prime $p$, a commutative ring $B$ and a ring homomorphism $j : \mathbb{Z}_{p^2} \to B$, where $\mathbb{Z}_{p^2}$ is realised as [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17), the Witt vectors of the field with $p^2$ elements. Let $X$ and $Y$ be formal $\mathcal{O}_D$-modules over $B$ in the sense of `FormalODModule`, i.e. each carries a two-dimensional commutative formal group law together with a multiplicative and additive action of $\mathbb{Z}_{p^2}$ by endomorphism series and an endomorphism series $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\mathrm{Frob}(a)]\circ\varpi$. Let $\theta : X \to Y$ be a homomorphism of formal $\mathcal{O}_D$-modules which is an isomorphism, in the sense that some $g : Y \to X$ satisfies $g\circ\theta = \mathrm{id}_X$ and $\theta\circ g = \mathrm{id}_Y$. Let $\gamma : \mathrm{Fin}\,2 \to$ [`MvFormalGroup.CartierModule p X.F`](def/MvFormalGroup_CartierModule.html#L162) be a homogeneous $V$-basis of the Cartier module of $X$ relative to $j$, i.e. $\gamma_i$ lies in the graded piece `X.gradedPiece j i` for each $i$, and the $2\times 2$ matrix of tangents $(\mathrm{tangent}(\gamma_i)_k)_{i,k}$ has unit determinant. Let $a : \mathbb{N} \to \mathrm{Fin}\,2 \to B$ be structure constants for $\gamma$, meaning that for every $i$ and every $N$ there is an element $h$ of the Cartier module with $\varpi_{*}\gamma_i = \sum_{m<N} V^{m}\bigl(a_{m,i}\cdot\gamma_{\mathrm{piIndex}(m,i)}\bigr) + V^{N}h$, where $V$ is `verschiebungInt` and $\varpi_{*}$ is the action `endAct X.varpiEnd`. Then the images $\mathrm{map}(\theta_{\mathrm{law}})(\gamma_i)$ under the additive map on Cartier modules induced by the underlying homomorphism of formal group laws `θ.toLawHom` form a homogeneous $V$-basis of the Cartier module of $Y$ relative to $j$, with the same structure constants $a$.
--
--   This is the statement that the Cartier-module functor transports the data of a homogeneous $V$-basis with prescribed structure constants along an isomorphism of formal $\mathcal{O}_D$-modules, in the Cartier-theoretic description of Drinfeld's special formal modules. It is used to move such bases and constants across the comparison isomorphisms coming from pro-representability of the deformation functor, in the construction of homogeneous $V$-bases with prescribed structure constants and in the surjectivity statement for the associated power-series presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso.lean

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

theorem CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X Y : CerednikDrinfeld.FormalODModule p B) (θ : X.Hom Y) (hθ : θ.IsIso)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (a : ℕ → Fin 2 → B) (ha : X.HasStructureConstants γ a) :
    Y.IsHomogeneousVBasis j (fun i => MvFormalGroup.CartierModule.map θ.toLawHom (γ i)) ∧
      Y.HasStructureConstants (fun i => MvFormalGroup.CartierModule.map θ.toLawHom (γ i)) a := by sorry
