-- Prove2me | Theorems.Thm_AlgebraicGeometry_isClosedImmersion_of_universallyClosed_of_universallyInjective_of_formallyUnramified
-- name    : AlgebraicGeometry.isClosedImmersion_of_universallyClosed_of_universallyInjective_of_formallyUnramified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/c330f943-ca41-5b87-b7e0-d2398b3fd901
-- title:
--   Universally closed, universally injective unramified morphisms are closed immersions
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe) and let $f : X \to Y$ be a morphism of schemes. Assume four properties of $f$, each recorded as a Mathlib class: $f$ is universally closed, i.e. every base change of $f$ is a closed map; $f$ is universally injective, i.e. every base change of $f$ is injective on points; $f$ is locally of finite type; and $f$ is formally unramified, i.e. it has the infinitesimal lifting uniqueness property against nilpotent thickenings. The conclusion is that $f$ is a closed immersion, in the sense of Mathlib's `IsClosedImmersion`: the underlying continuous map is a closed embedding and the map of structure sheaves is surjective. Thus the statement combines the hypotheses 'unramified' (formally unramified plus locally of finite type) with universal closedness and universal injectivity to obtain a closed immersion; no quasi-compactness or separatedness hypothesis is imposed, these being consequences of the assumptions.
--
--   This is the standard characterisation of closed immersions among universally closed morphisms (Grothendieck, EGA IV₄ 17.2.6, 18.12.6; Stacks Project, Tag 04XV). It is used in the project to deduce that a proper morphism all of whose geometric fibres are closed immersions is itself a closed immersion, in [`AlgebraicGeometry.isClosedImmersion_of_isProper_of_forall_geometricFibre_isClosedImmersion`](thm.html#AlgebraicGeometry.isClosedImmersion_of_isProper_of_forall_geometricFibre_isClosedImmersion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isClosedImmersion_of_universallyClosed_of_universallyInjective_of_formallyUnramified.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isClosedImmersion_of_universallyClosed_of_universallyInjective_of_formallyUnramified
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyClosed f] [UniversallyInjective f] [LocallyOfFiniteType f] [FormallyUnramified f] :
    IsClosedImmersion f := by sorry
