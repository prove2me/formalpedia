-- Prove2me | Theorems.Thm_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen
-- name    : AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_flat_of_universallyOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/e560d21e-1a1b-5cf4-baa1-0d081ac4bcec
-- title:
--   Integrality of the source of a flat, universally open, geometrically integral morphism
-- statement:
--   Let $X$ and $S$ be schemes (in a fixed universe) and let $f \colon X \to S$ be a morphism of schemes. Assume that $f$ is geometrically integral, i.e. has the property `GeometricallyIntegral` asserting that the geometric fibres of $f$ are integral; that $f$ is flat; and that $f$ is universally open, i.e. every base change of $f$ is an open map. Assume moreover that the base $S$ is an integral scheme, in the sense of Mathlib's `IsIntegral` for schemes. The conclusion is that $X$ is then itself an integral scheme. All four hypotheses are carried as typeclass assumptions on $f$ and on $S$. No Noetherian or finiteness hypothesis is imposed on $S$ or on $f$; in particular this is a strengthening of the variant in which $S$ is assumed locally Noetherian, the Noetherian assumption being replaced here by the observation that an irreducible base automatically has only finitely many irreducible components.
--
--   This is the standard descent statement that integrality of the base propagates to the source along a flat, universally open morphism with integral geometric fibres, here in the form with no Noetherian hypothesis on the base. It is used in the project as a source of integrality for total spaces of families of curves and of relative Picard constructions, being cited by results on constant reduction of curves, on Euler characteristics of sections of relative Picard schemes, and on smooth proper curves over algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_flat_of_universallyOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [GeometricallyIntegral f] [Flat f] [UniversallyOpen f]
    [IsIntegral S] : IsIntegral X := by sorry
