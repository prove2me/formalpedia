-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
-- name    : AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/711d8e74-27f4-5b30-855b-de17da74502e
-- title:
--   Smooth of relative dimension n over a field forces dim X ≥ n
-- statement:
--   Let $K$ be a field and let $X$ be a scheme, both in a fixed universe, and let $f \colon X \to \operatorname{Spec} K$ be a morphism of schemes, where $\operatorname{Spec} K$ is the spectrum of $K$ viewed as a commutative ring object. Fix a natural number $n$, assume that $f$ is smooth of relative dimension $n$ in the sense of the Mathlib class `SmoothOfRelativeDimension`, i.e. every point of $X$ has an affine open neighbourhood on which $f$ is given by a ring map which is standard smooth of relative dimension $n$, and assume that the underlying topological space of $X$ is non-empty. The conclusion is the inequality $n \le \operatorname{topologicalKrullDim} X$ in $\mathbb{N}_\infty$ adjoined a bottom element, where $\operatorname{topologicalKrullDim} X$ is the supremum of the lengths of strictly increasing chains of irreducible closed subsets of the space $X$ (the bottom element $\bot$ being the value for the empty space) and the natural number $n$ is coerced into that order. Only the lower bound is asserted; the matching upper bound $\dim X \le n$ is not part of this statement.
--
--   This is the lower-bound half of the classical statement that a non-empty scheme smooth of relative dimension $n$ over a field has dimension exactly $n$. It is used in this development to identify the integer $n$ appearing in smoothness of relative dimension $n$ with the geometric dimension, for instance for abelian varieties and in the analysis of fibres and of clopen decompositions of relative dimension one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Nonempty X] :
    (n : WithBot ℕ∞) ≤ topologicalKrullDim X := by sorry
