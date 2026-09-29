-- Prove2me | Theorems.Thm_AlgebraicGeometry_smooth_of_locallyOfFinitePresentation_of_forall_isClosed_formallySmooth_stalkMap
-- name    : AlgebraicGeometry.smooth_of_locallyOfFinitePresentation_of_forall_isClosed_formallySmooth_stalkMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/cedbdbfb-4510-58f0-9da2-56e05ad8a31d
-- title:
--   Smoothness from formal smoothness at closed points
-- statement:
--   Let $X$ and $S$ be schemes (in a fixed universe) and let $f : X \to S$ be a morphism of schemes which is locally of finite presentation, and suppose the underlying topological space of $X$ is a Jacobson space, that is, its closed points are dense in every closed subset. Assume that for every point $x$ of $X$ whose singleton $\{x\}$ is closed in $X$, the induced local ring homomorphism on stalks $\mathcal{O}_{S, f(x)} \to \mathcal{O}_{X,x}$ (the underlying ring map of `f.stalkMap x`) is formally smooth in the sense of Mathlib's `Algebra.FormallySmooth` for the corresponding algebra structure. Then $f$ is smooth, i.e. the typeclass `Smooth f` holds. Thus formal smoothness of the stalk maps need only be checked at the closed points of $X$, and no hypothesis at non-closed points is imposed.
--
--   This is the standard reduction of smoothness of a morphism locally of finite presentation to a pointwise condition at closed points, available because the smooth locus is open and closed points are dense in closed subsets of a Jacobson space (compare EGA IV₄ 17.5.1). It is used in the project to obtain smoothness from a lifting criterion tested on Artinian local rings, in [`AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_charP_of_finiteType_int`](thm.html#AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_charP_of_finiteType_int).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_smooth_of_locallyOfFinitePresentation_of_forall_isClosed_formallySmooth_stalkMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.smooth_of_locallyOfFinitePresentation_of_forall_isClosed_formallySmooth_stalkMap
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] [JacobsonSpace ↑X]
    (h : ∀ x : ↑X, IsClosed ({x} : Set ↑X) → (f.stalkMap x).hom.FormallySmooth) :
    Smooth f := by sorry
