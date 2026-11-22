-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_noetherian_affineModels_of_isProper
-- name    : AlgebraicGeometry.Scheme.nonempty_noetherian_affineModels_of_isProper
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-22T02:31:05.210235+00:00
-- url     : https://prove2.me/theorems/f63b2a7b-0e1b-4dd2-acc6-f880cb16fce6
-- title:
--   Affine Noetherian approximation of a proper morphism
-- statement:
--   A proper scheme over an affine scheme is an inverse limit of proper schemes over Noetherian affine schemes with affine transition maps on the sources. The original base ring is the filtered colimit of the stage rings, and the limit maps commute over the base.
-- source:
--   Stacks Project, Lemma 32.13.3, https://stacks.math.columbia.edu/tag/0A0P, with affine base stages.

import Definitions.Def_AlgebraicGeometry_Scheme_ProperAffineModels

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.nonempty_noetherian_affineModels_of_isProper
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] :
    Nonempty (PhilipponProperAffineApproximation.AffineModels f) := by sorry
