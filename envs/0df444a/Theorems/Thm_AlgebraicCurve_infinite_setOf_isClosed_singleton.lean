-- Prove2me | Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
-- name    : AlgebraicCurve.infinite_setOf_isClosed_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/4876a12a-a9fe-5f4d-90e6-6979b9f98d6c
-- title:
--   A smooth curve over a field has infinitely many closed points
-- statement:
--   Let $k$ be a field and let $C$ be a scheme over the same universe, equipped with a morphism $c : C \to \operatorname{Spec} k$ (where $k$ is regarded as a commutative ring object). Assume $C$ is integral, i.e. reduced and irreducible, and that $c$ is smooth of relative dimension $1$ in Mathlib's sense, so that $C$ is covered by affine opens on which the structure morphism is standard smooth of relative dimension one. The conclusion is that the set $\{x \in C \mid \{x\} \text{ is closed in } C\}$ of closed points of the underlying topological space of $C$ is an infinite set. No properness or separatedness hypothesis is imposed: the affine line over any field already satisfies the conclusion.
--
--   This is the standard fact that a smooth curve over a field has infinitely many closed points; on an integral such curve the closed points are exactly the points other than the generic point. It is used throughout the geometric part of the development, for instance to find affine opens avoiding prescribed finite sets of points and in the analysis of relative effective Cartier divisors and of branch ideals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry Polynomial

theorem AlgebraicCurve.infinite_setOf_isClosed_singleton
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] :
    {x : C | IsClosed ({x} : Set C)}.Infinite := by sorry
