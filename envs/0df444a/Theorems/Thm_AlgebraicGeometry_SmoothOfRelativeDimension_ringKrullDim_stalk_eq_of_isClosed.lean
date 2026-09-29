-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_ringKrullDim_stalk_eq_of_isClosed
-- name    : AlgebraicGeometry.SmoothOfRelativeDimension.ringKrullDim_stalk_eq_of_isClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/2f95e3ba-1508-514d-b34d-dcab4cd48399
-- title:
--   Krull dimension of the stalk at a closed point of a smooth k-scheme
-- statement:
--   Let $k$ be a field, let $X$ be a scheme and let $f : X \to \operatorname{Spec} k$ be a morphism of schemes which is smooth of relative dimension $g$ for a natural number $g$ (Mathlib's `SmoothOfRelativeDimension g f`, here an instance hypothesis; the target is the spectrum of $k$ viewed as a commutative ring object). Let $x$ be a point of $X$ whose singleton $\{x\}$ is closed in the topological space of $X$. The conclusion is that the Krull dimension of the local ring $\mathcal{O}_{X,x}$, that is the stalk of the structure presheaf of $X$ at $x$, equals $g$. Both sides are compared in `WithBot ℕ∞`, the value group of `ringKrullDim`, with $g$ coerced from the natural numbers; in particular the assertion includes that this dimension is finite and not $\bot$. No Noetherian, separatedness, finite-type or irreducibility hypotheses beyond those implied by smoothness of relative dimension $g$ over a field are imposed, and the point $x$ need not be a rational point.
--
--   This is the standard computation that a scheme smooth of relative dimension $g$ over a field is $g$-dimensional at each of its closed points, so that closed points are exactly the points of codimension $g$. It is used in the dimension bookkeeping for polarised abelian schemes, where it feeds the Euler-characteristic computation for Mumford bundles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_ringKrullDim_stalk_eq_of_isClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.SmoothOfRelativeDimension.ringKrullDim_stalk_eq_of_isClosed
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (g : ℕ) [SmoothOfRelativeDimension g f] (x : X) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = g := by sorry
