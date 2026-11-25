-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_cohomology_preimage_of_filtered_coefficients_pullback
-- name    : AlgebraicGeometry.Scheme.exists_cohomology_preimage_of_filtered_coefficients_pullback
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-25T08:41:11.96362+00:00
-- url     : https://prove2.me/theorems/c98791f2-347b-5759-9000-e6f9e8abd4e3
-- title:
--   Étale classes on an affine scheme lift to a filtered coefficient term
-- statement:
--   Let $Z\to X$ be a scheme morphism with affine source. Write an abelian étale sheaf on $X$ as a filtered colimit. Then a cohomology class on $Z$ with coefficients in its inverse image is the image of a class in the inverse image of one colimit term.
-- source:
--   Stacks Project, Lemma 59.51.4, https://stacks.math.columbia.edu/tag/03Q5.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Mathlib.CategoryTheory.ObjectProperty.Ind

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves)
universe u

theorem AlgebraicGeometry.Scheme.exists_cohomology_preimage_of_filtered_coefficients_pullback
    {J : Type u} [Category.{u} J] [IsFiltered J] {X Z : Scheme.{u}} [IsAffine Z] (i : Z ⟶ X)
    (F : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (d : Cocone F) (_ : IsColimit d)
    (q : ℕ) (x : ((pullbackSheaves i).obj d.pt).H q) :
    ∃ (j : J) (y : ((pullbackSheaves i).obj (F.obj j)).H q),
      Sheaf.H.map ((pullbackSheaves i).map (d.ι.app j)) q y = x := by sorry
