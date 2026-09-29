-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
-- name    : AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/76a81d88-5629-50aa-a4fe-85fedae12c73
-- title:
--   Nonempty connected scheme smooth over a field is integral
-- statement:
--   Let $k$ be a field and let $X$ be a scheme, both in the same universe, and let $f : X \to \operatorname{Spec} k$ be a morphism of schemes, where $\operatorname{Spec} k$ is the spectrum of $k$ viewed as a commutative ring object. Assume $f$ is smooth, that the underlying topological space of $X$ is preconnected (any two nonempty open sets covering $X$ meet, i.e. connectedness without the nonemptiness clause), and that $X$ is nonempty. The conclusion is that $X$ is an integral scheme in Mathlib's sense: $X$ is nonempty, its underlying space is irreducible, and $X$ is reduced. The hypotheses `PreconnectedSpace X` and `Nonempty X` together are exactly connectedness of $X$; the nonemptiness assumption cannot be dropped, since integrality includes it. No finiteness or quasi-compactness hypothesis on $X$ is imposed beyond what smoothness over $k$ supplies.
--
--   This is the standard fact that a scheme smooth over a field is regular, hence normal with domain local rings, so that connectedness upgrades it to integrality. It is used throughout the project to supply integrality, and thence irreducibility of the underlying space, for group schemes and for fibres of smooth families arising in the study of relative Picard schemes and polarisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [Smooth f] [PreconnectedSpace X] [Nonempty X] : IsIntegral X := by sorry
