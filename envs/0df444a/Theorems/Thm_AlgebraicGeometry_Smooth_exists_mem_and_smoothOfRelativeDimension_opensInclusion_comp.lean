-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp
-- name    : AlgebraicGeometry.Smooth.exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/5ce73455-0586-5518-98b7-0e39bb578d13
-- title:
--   Smooth morphisms are locally of some relative dimension
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe), let $f : X \to Y$ be a morphism which is smooth in the sense of Mathlib's `Smooth` morphism property, and let $x$ be a point of $X$. Then there exist an open subscheme $V$ of $X$ and a natural number $d$ such that $x \in V$ and the composite of the open immersion $V.\iota : V \to X$ with $f$, that is $f \circ V.\iota$, is smooth of relative dimension $d$ in the sense of `SmoothOfRelativeDimension`. Thus smoothness, which imposes no uniformity on the relative dimension, can be refined near any prescribed point to smoothness of one fixed relative dimension, the open set $V$ and the integer $d$ both being allowed to depend on $x$. No connectedness or finiteness hypothesis on $X$ or $Y$ is assumed, and the statement asserts nothing about the value of $d$ beyond its existence.
--
--   This is the standard local normalisation of a smooth morphism: smoothness is local on the source and each local chart has a well-defined relative dimension, so every point has a neighbourhood on which the morphism is smooth of constant relative dimension. It is used in the study of the locus where the fibre dimension of a smooth proper morphism is constant and in the construction of the relative group law on Jacobians, via [`AlgebraicGeometry.isClopen_setOf_topologicalKrullDim_preimage_eq_of_smooth_of_isProper`](thm.html#AlgebraicGeometry.isClopen_setOf_topologicalKrullDim_preimage_eq_of_smooth_of_isProper) and [`GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Smooth.exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ SmoothOfRelativeDimension d (V.ι ≫ f) := by sorry
