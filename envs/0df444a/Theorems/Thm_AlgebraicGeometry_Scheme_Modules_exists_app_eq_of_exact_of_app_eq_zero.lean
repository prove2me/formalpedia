-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero
-- name    : AlgebraicGeometry.Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/46d21967-b588-5947-b6df-00effa79bf18
-- title:
--   Left exactness of sections over an open on 𝒪_X-modules
-- statement:
--   Let $X$ be a scheme and let $S$ be a short complex in the category `X.Modules` of sheaves of $\mathcal{O}_X$-modules, that is, a pair of composable morphisms $S.f : S.X_1 \to S.X_2$ and $S.g : S.X_2 \to S.X_3$ whose composite is zero. Assume $S$ is exact in the sense of Mathlib's `ShortComplex.Exact` for this abelian category, and assume moreover that $S.f$ is a monomorphism. Let $U$ be an open subset of $X$ and let $m \in \Gamma(S.X_2, U)$ be a section of the middle sheaf over $U$ whose image under the map on sections $S.g.app\ U$ vanishes. Then there exists a section $e \in \Gamma(S.X_1, U)$ with $S.f.app\ U\ e = m$. Thus only exactness at the middle term of the sequence of sections over $U$ is asserted; injectivity of $S.f.app\ U$ and surjectivity of $S.g.app\ U$ are not part of the conclusion (the latter being false in general).
--
--   This is the left exactness of the functor of sections over an open $U$ on sheaves of $\mathcal{O}_X$-modules, in the form of a lifting statement for sections killed by the second map. It is used in the project wherever a local section of the middle sheaf of an exact sequence must be lifted, for instance in the treatment of short exact sequences of module sheaves under pushforward, in wedge-power arguments for vector bundles, and in Euler-characteristic computations for invertible ideal sheaves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero
    {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.Exact) [Mono S.f]
    (U : X.Opens) (m : Γ(S.X₂, U)) (hm : S.g.app U m = 0) :
    ∃ e : Γ(S.X₁, U), S.f.app U e = m := by sorry
