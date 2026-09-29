-- Prove2me | Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_forall_fiber
-- name    : AlgebraicGeometry.smoothOfRelativeDimension_of_smooth_of_forall_fiber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/f7100c74-6ac7-5129-8873-b2cf4402dff6
-- title:
--   Fibrewise relative dimension for smooth morphisms
-- statement:
--   Let $f : X \to Y$ be a morphism of schemes (in a fixed universe) which is assumed smooth, and let $n$ be a natural number. Suppose that for every point $y$ of $Y$ the induced morphism `f.fiberToSpecResidueField y` from the scheme-theoretic fibre of $f$ over $y$ to $\operatorname{Spec}$ of the residue field $\kappa(y)$ is smooth of relative dimension $n$, i.e. every point of the fibre has an affine open neighbourhood $V'$ mapping into an affine open $U'$ of $\operatorname{Spec}\kappa(y)$ such that the corresponding ring map $\Gamma(\operatorname{Spec}\kappa(y),U') \to \Gamma(X_y,V')$ is standard smooth of relative dimension $n$. Then $f$ itself is smooth of relative dimension $n$: for every $x \in X$ there are affine opens $U \subseteq Y$ and $V \subseteq X$ with $x \in V$ and $V \subseteq f^{-1}(U)$ such that the induced ring map $\Gamma(Y,U) \to \Gamma(X,V)$ is standard smooth of relative dimension $n$. Note that smoothness of $f$ is a hypothesis, not a conclusion; only the relative dimension is deduced from the fibres.
--
--   This is the fibrewise determination of the relative dimension of a smooth morphism: smoothness being known, the common relative dimension $n$ of all fibres is the relative dimension of the morphism. It is used in the treatment of relative group laws on Jacobians of curves with good reduction, where relative dimension of a smooth morphism is checked on fibres, via the Krull-dimension and formal-coordinates criteria.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_forall_fiber.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.smoothOfRelativeDimension_of_smooth_of_forall_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (n : ℕ)
    (h : ∀ y : Y, SmoothOfRelativeDimension n (f.fiberToSpecResidueField y)) :
    SmoothOfRelativeDimension n f := by sorry
