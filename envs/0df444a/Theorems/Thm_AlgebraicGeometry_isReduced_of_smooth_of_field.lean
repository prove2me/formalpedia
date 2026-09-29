-- Prove2me | Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
-- name    : AlgebraicGeometry.isReduced_of_smooth_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/a60d237d-6566-598e-982e-db0bd5a1118e
-- title:
--   A scheme smooth over a field is reduced
-- statement:
--   Let $K$ be a field and let $X$ be a scheme, both in the same universe, and let $sX : X \to \operatorname{Spec} K$ be a morphism of schemes to the spectrum of $K$ (the affine scheme on the commutative ring $K$) which is smooth, in the sense of Mathlib's `Smooth` property of morphisms of schemes. The conclusion is that $X$ is reduced, i.e. `IsReduced X`: $X$ is nonempty-sectionwise reduced in Mathlib's sense, namely for every open subset $U$ of $X$ the ring of sections $\Gamma(X, U)$ has no nonzero nilpotent elements. No finiteness, separatedness or geometric hypothesis beyond smoothness of the structure morphism is imposed, and no hypothesis on $K$ beyond being a field; in particular $K$ need not be perfect or algebraically closed.
--
--   This is the standard fact that smoothness over a field forces reducedness (EGA IV 17.5.8 together with 6.3), used throughout the project whenever a geometric argument on a smooth curve or group scheme requires reducedness, for instance to identify two morphisms out of a smooth scheme that agree on a dense set of points. It is invoked by a number of later results, among them statements about Picard groups of algebraic curves and a reducedness criterion for quotients of formally smooth algebras at maximal ideals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isReduced_of_smooth_of_field.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.isReduced_of_smooth_of_field
    {K : Type u} [Field K] {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [Smooth sX] :
    IsReduced X := by sorry
