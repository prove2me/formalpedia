-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace
-- name    : AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/cb52222f-94d6-5f1e-a5ee-7cc3c2bb1459
-- title:
--   Smooth morphism with preconnected source has constant relative dimension
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe) and let $f\colon X \to Y$ be a morphism of schemes which is smooth, i.e. satisfies the Mathlib class `Smooth`, so that every point of $X$ lies in an affine open $V$ mapping into an affine open $U$ of $Y$ for which the induced ring map $\Gamma(Y,U) \to \Gamma(X,V)$ is standard smooth (of some, a priori point-dependent, relative dimension). Assume moreover that the underlying topological space of $X$ is preconnected, in the sense of the class `PreconnectedSpace`; this allows $X$ to be empty. The conclusion is that there is a single natural number $n$ such that `SmoothOfRelativeDimension n f` holds, i.e. every point $x$ of $X$ admits an affine open $V \subseteq X$ containing $x$ and an affine open $U \subseteq Y$ with $V \subseteq f^{-1}(U)$ such that the induced map $\Gamma(Y,U) \to \Gamma(X,V)$ is standard smooth of relative dimension exactly $n$. Thus the relative dimension may be chosen uniformly over all of $X$.
--
--   This is the local constancy of the relative dimension of a smooth morphism (EGA IV$_4$, 17.10.2), in the form that allows the global relative dimension of a smooth morphism with connected source to be named. It is used in the project to supply relative dimension $1$ for smooth loci of curves and their semistable models, where stalks at points of the smooth locus are analysed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [PreconnectedSpace X] :
    ∃ n : ℕ, SmoothOfRelativeDimension n f := by sorry
