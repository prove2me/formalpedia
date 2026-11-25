-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_etale_H_zero_preimage_of_filtered_coefficients
-- name    : AlgebraicGeometry.Scheme.exists_etale_H_zero_preimage_of_filtered_coefficients
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-25T20:07:20.19094+00:00
-- url     : https://prove2.me/theorems/b6eb167d-bd75-4936-a4f9-8255c8af0d21
-- title:
--   Global étale sections on an affine scheme lift to a filtered coefficient term
-- statement:
--   Let X be affine and write an abelian étale sheaf on X as a filtered colimit. Each degree-zero cohomology class is the image of a class for one term.
-- source:
--   Stacks Project, Lemma 59.51.4, https://stacks.math.columbia.edu/tag/03Q5.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Mathlib.CategoryTheory.ObjectProperty.Ind

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves)
universe u

theorem AlgebraicGeometry.Scheme.exists_etale_H_zero_preimage_of_filtered_coefficients
    {J : Type u} [Category.{u} J] [IsFiltered J]
    (X : Scheme.{u}) [IsAffine X] (F : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (d : Cocone F) (_ : IsColimit d) (x : d.pt.H 0) :
    ∃ (j : J) (y : (F.obj j).H 0), Sheaf.H.map (d.ι.app j) 0 y = x := by sorry
