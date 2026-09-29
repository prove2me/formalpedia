-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
-- name    : AlgebraicGeometry.Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/7bb92d34-b510-5433-b2be-11034d011018
-- title:
--   Morphisms matching frames on a cover are isomorphisms
-- statement:
--   Let $X$ be a scheme and let $\mu \colon P \to Q$ be a morphism of sheaves of $\mathcal{O}_X$-modules on $X$ (objects of `X.Modules`). Let $\iota$ be a type in an arbitrary universe and let $\mathcal{V} \colon \iota \to$ `X.Opens` be a family of open subsets of $X$ with $\bigsqcup_i \mathcal{V}_i = \top$, i.e. the $\mathcal{V}_i$ cover $X$. Suppose given sections $p_i \in \Gamma(P, \mathcal{V}_i)$ and $q_i \in \Gamma(Q, \mathcal{V}_i)$ for each $i$ such that `IsFrameOn` holds for $p_i$ on $\mathcal{V}_i$ and for $q_i$ on $\mathcal{V}_i$; by definition this means that for every open $W \le \mathcal{V}_i$ the map $\Gamma(X, W) \to \Gamma(P, W)$, $g \mapsto g \cdot (p_i|_W)$, is bijective, and likewise $g \mapsto g \cdot (q_i|_W)$ is a bijection $\Gamma(X, W) \to \Gamma(Q, W)$. Suppose finally that the component of $\mu$ over $\mathcal{V}_i$ carries $p_i$ to $q_i$, that is $\mu_{\mathcal{V}_i}(p_i) = q_i$ for all $i$. Then $\mu$ is an isomorphism in the category of sheaves of $\mathcal{O}_X$-modules on $X$.
--
--   This is the standard local criterion for a morphism of $\mathcal{O}_X$-modules to be an isomorphism: if both sheaves are free of rank one on the members of a cover, with frames matched by the morphism, then the morphism is invertible. It serves as the basic recognition tool for trivialisations of line bundles and is used, among other places, in the treatment of rigidified line bundles and relative Picard functors and in criteria for pullbacks of line bundles to be isomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top
    {X : Scheme.{u}} {P Q : X.Modules} (μ : P ⟶ Q) {ι : Type v} (𝒱 : ι → X.Opens) (hcov : ⨆ i, 𝒱 i = ⊤)
    (p : ∀ i, Γ(P, 𝒱 i)) (q : ∀ i, Γ(Q, 𝒱 i))
    (hp : ∀ i, Scheme.Modules.IsFrameOn (p i) (𝒱 i)) (hq : ∀ i, Scheme.Modules.IsFrameOn (q i) (𝒱 i))
    (hμ : ∀ i, μ.app (𝒱 i) (p i) = q i) : IsIso μ := by sorry
