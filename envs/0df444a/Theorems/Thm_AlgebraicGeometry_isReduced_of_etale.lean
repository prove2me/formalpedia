-- Prove2me | Theorems.Thm_AlgebraicGeometry_isReduced_of_etale
-- name    : AlgebraicGeometry.isReduced_of_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/8cdd0657-520e-52d7-a465-7cd44bf53a74
-- title:
--   Étale over reduced locally Noetherian is reduced
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe) and let $f \colon X \to Y$ be a morphism of schemes which is étale, in the sense of the `Etale` class for scheme morphisms. Assume in addition that $Y$ is reduced and that $Y$ is locally Noetherian, i.e. satisfies `IsLocallyNoetherian`. The conclusion is that $X$ is reduced. Both reducedness hypothesis and conclusion are the Mathlib predicate `IsReduced` on schemes; no finiteness, separatedness or quasi-compactness assumption is made on $f$ beyond étaleness, and no hypothesis is imposed directly on $X$. Note that the local Noetherian hypothesis on $Y$ is genuinely assumed here, although the classical statement (EGA IV 17.5.7) needs no Noetherian hypothesis; it enters through the ring-theoretic input used in the proof.
--
--   This is the standard permanence statement that reducedness ascends along étale morphisms, here in a form carrying a local Noetherian hypothesis on the base. It is used in the project when transporting reducedness through étale charts, for instance in the analysis of relative effective Cartier divisors and line bundles and in the study of good reduction of Jacobians and of torsion on abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isReduced_of_etale.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isReduced_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsReduced Y] [IsLocallyNoetherian Y] :
    IsReduced X := by sorry
