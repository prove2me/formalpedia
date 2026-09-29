-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
-- name    : AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/de7870b0-9619-54d5-ade4-addae1c90a85
-- title:
--   Smooth of relative dimension n over a field: dim X ≤ n
-- statement:
--   Let $K$ be a field, let $X$ be a scheme and let $f \colon X \to \operatorname{Spec} K$ be a morphism of schemes, where $\operatorname{Spec} K$ is the spectrum of $K$ regarded as a commutative ring. Let $n$ be a natural number, and suppose that $f$ is smooth of relative dimension $n$ in the sense of Mathlib's class `SmoothOfRelativeDimension n f`, i.e. $f$ is locally, on suitable affine charts, given by a standard smooth algebra of relative dimension $n$. The conclusion is that the topological Krull dimension of the underlying topological space of $X$ — the supremum of the lengths of chains of irreducible closed subsets, taken in $\mathbb{Z} \cup \{\pm\infty\}$ — is at most $n$. Only this upper bound is asserted; the classical statement that every non-empty open subset of such an $X$ has dimension exactly $n$ is not claimed, and in particular the empty scheme, for which the dimension is $-\infty$, is permitted.
--
--   This is the dimension bound for smooth varieties over a field: a scheme smooth of relative dimension $n$ over $\operatorname{Spec} K$ has dimension at most $n$. It underlies the dimension-theoretic facts used for curves and their Jacobians elsewhere in the development, for instance in identifying the Krull dimension of local rings at closed points and the dimension of fibres of smooth morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f] :
    topologicalKrullDim X ≤ n := by sorry
