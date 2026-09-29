-- Prove2me | Theorems.Thm_AlgebraicGeometry_isOpenImmersion_and_isClosedImmersion_of_comp_eq_id
-- name    : AlgebraicGeometry.isOpenImmersion_and_isClosedImmersion_of_comp_eq_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/07d17e45-7cc4-5648-bc55-62923b220075
-- title:
--   Sections of separated unramified morphisms are open and closed immersions
-- statement:
--   Let $S$ and $T$ be schemes and let $g \colon T \to S$ be a morphism of schemes which is locally of finite type (`LocallyOfFiniteType`), formally unramified (`FormallyUnramified`) and separated (`IsSeparated`). Let $s \colon S \to T$ be a morphism such that $s$ followed by $g$ is the identity of $S$, i.e. $g \circ s = \mathrm{id}_S$, so that $s$ is a section of $g$. The conclusion is the conjunction of two assertions about $s$ itself: $s$ is an open immersion, and $s$ is a closed immersion. In particular the image of $s$ is an open and closed subscheme of $T$ which $g$ carries isomorphically onto $S$. The finite-type and formal unramifiedness hypotheses on $g$ serve the open-immersion half, and separatedness serves the closed-immersion half; both halves are asserted simultaneously here.
--
--   This is the standard statement that a section of an unramified separated morphism is an open and closed immersion (for example for $g$ étale and separated). It is used in the construction of an open piece of a pullback over which a twist becomes isomorphic to the unit object, in [`MvPolynomial.CrossingQuotient.Resolution.exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero`](thm.html#MvPolynomial.CrossingQuotient.Resolution.exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isOpenImmersion_and_isClosedImmersion_of_comp_eq_id.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isOpenImmersion_and_isClosedImmersion_of_comp_eq_id
    {S T : Scheme.{u}} (g : T ⟶ S) [LocallyOfFiniteType g] [FormallyUnramified g] [IsSeparated g]
    (s : S ⟶ T) (hs : s ≫ g = 𝟙 S) :
    IsOpenImmersion s ∧ IsClosedImmersion s := by sorry
