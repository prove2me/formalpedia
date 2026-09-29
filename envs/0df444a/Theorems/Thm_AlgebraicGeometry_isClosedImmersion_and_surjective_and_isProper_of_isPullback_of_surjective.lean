-- Prove2me | Theorems.Thm_AlgebraicGeometry_isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective
-- name    : AlgebraicGeometry.isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/49a49770-04fc-55b5-be00-6e51a987da0b
-- title:
--   Properness descends through a surjective closed immersion of the base
-- statement:
--   Let $S$, $S_0$, $X$, $X_0$ be schemes (in a fixed universe), let $i : S_0 \to S$ be a morphism that is a closed immersion and is surjective, and let $f : X \to S$, $f_0 : X_0 \to S_0$ and $g : X_0 \to X$ be morphisms such that the square with $g$, $f_0$, $f$, $i$ is a pullback square, i.e. $g$ followed by $f$ equals $f_0$ followed by $i$ and the square is cartesian. Then five conclusions hold simultaneously: $g$ is a closed immersion; $g$ is surjective; if $f_0$ is separated then $f$ is separated; if $f_0$ is universally closed then $f$ is universally closed; and if $f_0$ is proper and $f$ is locally of finite type then $f$ is proper. Thus the properties of separatedness, universal closedness and (given local finite type for $f$) properness transfer from the base change $f_0$ back to $f$ across a closed immersion $i$ which is a homeomorphism onto $S$.
--
--   This is the standard statement that separatedness, universal closedness and properness may be checked after base change along a surjective closed immersion, for instance along $\operatorname{Spec}(R/I) \to \operatorname{Spec} R$ with $I$ nilpotent; it is the form in which properness of a scheme over a ring is recovered from properness of its reduction modulo a nilpotent ideal. It is used in the deformation-theoretic study of abelian schemes and Jacobians with good reduction, where objects over an Artinian base are constructed by successive infinitesimal thickenings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective
    {S S₀ X X₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i] [Surjective i]
    {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : X₀ ⟶ X} (hg : IsPullback g f₀ f i) :
    IsClosedImmersion g ∧ Surjective g ∧ (IsSeparated f₀ → IsSeparated f) ∧
      (UniversallyClosed f₀ → UniversallyClosed f) ∧
      (IsProper f₀ → LocallyOfFiniteType f → IsProper f) := by sorry
