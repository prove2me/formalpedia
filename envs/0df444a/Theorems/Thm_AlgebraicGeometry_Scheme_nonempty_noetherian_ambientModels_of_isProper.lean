-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_noetherian_ambientModels_of_isProper
-- name    : AlgebraicGeometry.Scheme.nonempty_noetherian_ambientModels_of_isProper
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-22T00:19:59.419644+00:00
-- url     : https://prove2.me/theorems/73e2a8cb-0ccf-420b-8935-3bcb3148d282
-- title:
--   Noetherian local models of a proper morphism
-- statement:
--   A proper morphism to $\operatorname{Spec}(A)$, with $A$ local, is a cofiltered limit of proper morphisms to spectra of Noetherian local rings. The transition maps on the sources are affine, and the transition maps of base rings and their maps to $A$ are local.
-- source:
--   Stacks Project, Lemma 32.13.3, https://stacks.math.columbia.edu/tag/0A0P, using affine approximations and localizing each base at the image of the closed point.

import Definitions.Def_AlgebraicGeometry_Scheme_ProperAmbientModels

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.nonempty_noetherian_ambientModels_of_isProper
    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] :
    Nonempty (PhilipponProperAmbientModels.AmbientModels f) := by sorry
