-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/d942925a-3f48-50a6-b5da-5cedda207bd4
-- title:
--   Matching local frames forces a module morphism to be an isomorphism
-- statement:
--   Let $X$ be a scheme and let $P$ and $Q$ be sheaves of $\mathcal{O}_X$-modules on $X$ (objects of `X.Modules`), with $\mu : P \to Q$ a morphism between them. Let $\mathcal{V} : \iota \to$ `X.Opens` be a family of open subsets of $X$ indexed by an arbitrary type $\iota$, whose supremum is $\top$, i.e. the $\mathcal{V}_i$ cover $X$. Suppose given sections $p_i \in \Gamma(P, \mathcal{V}_i)$ and $q_i \in \Gamma(Q, \mathcal{V}_i)$ for every $i$, each of which is a frame on its own open set in the sense of `Scheme.Modules.IsFrameOn`: for every open $W \le \mathcal{V}_i$ the map $\Gamma(X, W) \to \Gamma(P, W)$, $g \mapsto g \cdot (p_i|_W)$, is bijective, and likewise $g \mapsto g \cdot (q_i|_W)$ is a bijection $\Gamma(X, W) \to \Gamma(Q, W)$. Suppose finally that the component of $\mu$ over $\mathcal{V}_i$ carries $p_i$ to $q_i$, that is $\mu_{\mathcal{V}_i}(p_i) = q_i$ for all $i$. Then $\mu$ is an isomorphism in the category of sheaves of $\mathcal{O}_X$-modules on $X$.
--
--   This is the local criterion identifying a morphism between two invertible (locally free of rank one) sheaves of modules as an isomorphism: it suffices that local generators be matched on a cover. It is used in the treatment of invertible sheaves and polarisations, for instance by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_of_isIso_pullbackSection_of_surjective`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_of_isIso_pullbackSection_of_surjective) and in the construction of sections of line bundles on elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top_monoidalV2
    {X : Scheme.{u}} {P Q : X.Modules} (μ : P ⟶ Q) {ι : Type v} (𝒱 : ι → X.Opens) (hcov : ⨆ i, 𝒱 i = ⊤)
    (p : ∀ i, Γ(P, 𝒱 i)) (q : ∀ i, Γ(Q, 𝒱 i))
    (hp : ∀ i, Scheme.Modules.IsFrameOn (p i) (𝒱 i)) (hq : ∀ i, Scheme.Modules.IsFrameOn (q i) (𝒱 i))
    (hμ : ∀ i, μ.app (𝒱 i) (p i) = q i) : IsIso μ := by sorry
