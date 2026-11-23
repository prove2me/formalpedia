-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_closedFiberModels_of_isProper
-- name    : AlgebraicGeometry.Scheme.nonempty_closedFiberModels_of_isProper
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-21T23:18:39.441435+00:00
-- url     : https://prove2.me/theorems/dd334e83-9ff0-4755-acdf-adf82eb12e89
-- title:
--   Approximate a proper closed fiber by proper Noetherian models
-- statement:
--   Let $X\to\operatorname{Spec}(A)$ be proper, where $A$ is a local ring. The closed fiber of $X$ is a cofiltered limit of the closed fibers of proper schemes over Noetherian local rings. The transition morphisms are affine and each projection of the closed-fiber limit is compatible with a morphism between the ambient schemes.
-- source:
--   Stacks Project, Lemma 32.13.3, https://stacks.math.columbia.edu/tag/0A0P, and the limit construction in Lemma 36.32.7, https://stacks.math.columbia.edu/tag/0G7X.

import Definitions.Def_AlgebraicGeometry_Scheme_ProperClosedFiberModels

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.nonempty_closedFiberModels_of_isProper
    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] :
    Nonempty (PhilipponProperClosedFiberApproximation.ClosedFiberModels
      (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) f)) := by sorry
