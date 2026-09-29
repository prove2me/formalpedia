-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_eq
-- name    : AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/cc8ee8fb-872d-599f-83c7-bd05f6f2166f
-- title:
--   Closed immersion of equal-rank finite flat schemes is an isomorphism
-- statement:
--   Let $X$, $Y$, $Z$ be schemes (in a fixed universe), let $fX : X \to Z$ and $fY : Y \to Z$ be morphisms, and let $i : X \to Y$ be a morphism with $i$ followed by $fY$ equal to $fX$, so that $i$ is a morphism over $Z$. Assume $i$ is a closed immersion, and assume that each of $fX$ and $fY$ is finite, flat and locally of finite presentation (finite locally free). Assume finally that the two structure morphisms have the same rank at every point of the base: for every $z \in Z$, the local rank $fX.\mathrm{finrank}\,z$ of $fX$ at $z$ equals $fY.\mathrm{finrank}\,z$, where `Scheme.Hom.finrank` is Mathlib's rank function for such a morphism at a point of the target. The conclusion is that $i$ is an isomorphism of schemes.
--
--   This is the standard rigidity statement that a closed subscheme of a finite locally free $Z$-scheme which is itself finite locally free of the same rank over $Z$ must be the whole scheme; concretely, over an affine chart it says that a surjection of finite projective modules of equal rank at each point is bijective. In this development it is used to identify moduli schemes of fake elliptic curves with extra level structure in the Čerednik–Drinfeld part of the argument, for instance when comparing pullback squares and Atkin–Lehner quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_eq
    {X Y Z : Scheme.{u}} (fX : X ⟶ Z) (fY : Y ⟶ Z) (i : X ⟶ Y) (hi : i ≫ fY = fX)
    [IsClosedImmersion i]
    [IsFinite fX] [Flat fX] [LocallyOfFinitePresentation fX]
    [IsFinite fY] [Flat fY] [LocallyOfFinitePresentation fY]
    (hrank : ∀ z : Z, fX.finrank z = fY.finrank z) :
    IsIso i := by sorry
