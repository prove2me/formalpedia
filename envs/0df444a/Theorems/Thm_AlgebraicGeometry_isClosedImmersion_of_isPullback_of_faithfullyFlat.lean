-- Prove2me | Theorems.Thm_AlgebraicGeometry_isClosedImmersion_of_isPullback_of_faithfullyFlat
-- name    : AlgebraicGeometry.isClosedImmersion_of_isPullback_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/15a640ab-f9cc-514b-bd68-f574dde1accc
-- title:
--   Closed immersions descend along faithfully flat base change
-- statement:
--   Let $S$ and $S'$ be commutative rings in a fixed universe, with $S'$ an $S$-algebra which is faithfully flat as an $S$-module. Let $X, Y, X', Y'$ be schemes and let $g : Y \to \operatorname{Spec} S$, $g' : Y' \to \operatorname{Spec} S'$ and $c_Y : Y' \to Y$ be morphisms such that the square formed by $c_Y$, $g'$, $g$ and $\operatorname{Spec}$ of the structure map $S \to S'$ is cartesian, i.e. $c_Y \circ$-composed with $g$ agrees with $g'$ followed by $\operatorname{Spec}(S \to S')$ and exhibits $Y'$ as the fibre product $Y \times_{\operatorname{Spec} S} \operatorname{Spec} S'$. Let further $i : X \to Y$, $i' : X' \to Y'$ and $c_X : X' \to X$ be morphisms such that the square formed by $c_X$, $i'$, $i$ and $c_Y$ is cartesian, so that $X'$ is the base change $X \times_Y Y'$ and $i'$ is the base change of $i$ along $c_Y$. The assertion is that if $i'$ is a closed immersion, then so is $i$.
--
--   This is the descent of the property 'closed immersion' along a faithfully flat affine base change $\operatorname{Spec} S' \to \operatorname{Spec} S$, in the form needed when a subscheme is only known to be closed after such a base change. It is used in the construction [`AlgebraicGeometry.Scheme.Modules.closedImmersionBySections_of_faithfullyFlat_of_isPullback`](thm.html#AlgebraicGeometry.Scheme.Modules.closedImmersionBySections_of_faithfullyFlat_of_isPullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isClosedImmersion_of_isPullback_of_faithfullyFlat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.isClosedImmersion_of_isPullback_of_faithfullyFlat
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X Y X' Y' : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of S)) (g' : Y' ⟶ Spec (CommRingCat.of S')) (cY : Y' ⟶ Y)
    (hY : IsPullback cY g' g (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (i : X ⟶ Y) (i' : X' ⟶ Y') (cX : X' ⟶ X) (hX : IsPullback cX i' i cY)
    (h : IsClosedImmersion i') :
    IsClosedImmersion i := by sorry
