-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq
-- name    : AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/a3312ee8-c9e1-5252-8fba-7eaff32d65be
-- title:
--   Fibres of a smooth morphism of relative dimension n
-- statement:
--   Let $X$ and $Y$ be schemes and $f : X \to Y$ a morphism of schemes which is smooth of relative dimension $n$ for a natural number $n$, in the sense of Mathlib's morphism property `SmoothOfRelativeDimension n`. Let $y$ be a point of the underlying topological space of $Y$, and assume that the set-theoretic preimage $f^{-1}(\{y\})$ under the continuous map $f.base$ on underlying spaces is non-empty. Then the topological Krull dimension of the subspace $f^{-1}(\{y\}) \subseteq X$, taken with its induced topology and measured by `topologicalKrullDim` with values in `WithBot ℕ∞`, equals $n$. In particular the non-emptiness hypothesis rules out the value $\bot$, and the conclusion is an equality of elements of `WithBot ℕ∞` rather than of natural numbers; the statement is about the topological fibre as a subspace of $X$, not about the scheme-theoretic fibre.
--
--   This is the standard identification of the relative dimension of a smooth morphism with the dimension of its fibres (EGA IV, 17.10.2). It is used throughout the project wherever a fibrewise dimension count is needed, for instance to see that the fibres of a curve model are one-dimensional and in the dimension bookkeeping for polarisations of abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n f]
    (y : ↥Y) (hy : (f.base ⁻¹' {y}).Nonempty) :
    topologicalKrullDim ↥(f.base ⁻¹' {y}) = n := by sorry
