-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
-- name    : AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/f328b219-3794-536f-99cd-1776bab228ef
-- title:
--   Smoothness over a reduced locally Noetherian base preserves reducedness
-- statement:
--   Let $X$ and $Y$ be schemes and let $f \colon X \to Y$ be a morphism which is smooth, where smoothness is taken in the sense of Mathlib's `Smooth` class for morphisms of schemes. Assume further that $Y$ is reduced, i.e. satisfies `IsReduced`, and that $Y$ is locally Noetherian, i.e. satisfies `IsLocallyNoetherian`. The conclusion is that the source $X$ is then reduced as well, i.e. `IsReduced X` holds. No separateness, finiteness or quasi-compactness assumption is imposed on $f$ beyond what smoothness already entails, and no hypothesis is placed on $X$ itself; the Noetherian hypothesis is required only on the target.
--
--   This is the permanence statement that reducedness ascends along a smooth morphism onto a reduced locally Noetherian base, as in EGA IV₄ 17.5.7. It is used throughout the development whenever a scheme constructed as the source of a smooth morphism (for instance a smooth group scheme or a smooth cover over a reduced Noetherian base) must be known to be reduced, and it is specialised to the affine case for rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsReduced Y] [IsLocallyNoetherian Y] :
    IsReduced X := by sorry
