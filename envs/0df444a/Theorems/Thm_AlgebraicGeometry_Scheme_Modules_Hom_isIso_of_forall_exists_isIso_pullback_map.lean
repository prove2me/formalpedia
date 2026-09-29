-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map
-- name    : AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_forall_exists_isIso_pullback_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/cac4d0ba-0c4b-58ee-bcad-c109378430dd
-- title:
--   Being an isomorphism is local for sheaves of modules
-- statement:
--   Let $X$ be a scheme, let $M$ and $N$ be sheaves of $\mathcal{O}_X$-modules (objects of `X.Modules`), and let $\varphi \colon M \to N$ be a morphism between them. Assume that for every point $x$ of $X$ there is an open subset $U$ of $X$ with $x \in U$ such that the image of $\varphi$ under the inverse-image functor `Scheme.Modules.pullback U.ι` along the open immersion $U \hookrightarrow X$ — that is, the restriction $\varphi|_U \colon M|_U \to N|_U$ as a morphism of $\mathcal{O}_U$-modules — is an isomorphism. The conclusion is that $\varphi$ itself is an isomorphism in `X.Modules`. Note that the open subsets $U$ are required only to cover $X$ pointwise, one for each point, and no compatibility between the chosen neighbourhoods or the inverses on them is assumed.
--
--   This is the standard statement that being an isomorphism of sheaves of modules is a local property on the base, in the inverse-image (restriction along an open immersion) phrasing. It is used in the treatment of invertible and locally free modules on schemes, where local data are given as trivialisations over members of an open cover; it is cited, for instance, in the results on invertible ideal sheaf data and on pushforwards of invertible modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_forall_exists_isIso_pullback_map
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIso ((Scheme.Modules.pullback U.ι).map φ)) :
    IsIso φ := by sorry
