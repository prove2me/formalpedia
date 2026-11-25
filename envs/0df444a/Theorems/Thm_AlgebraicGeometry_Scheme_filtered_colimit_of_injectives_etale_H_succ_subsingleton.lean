-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_filtered_colimit_of_injectives_etale_H_succ_subsingleton
-- name    : AlgebraicGeometry.Scheme.filtered_colimit_of_injectives_etale_H_succ_subsingleton
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-25T19:59:26.009438+00:00
-- url     : https://prove2.me/theorems/e2769a5e-6319-4ce9-a2a7-25938164aec1
-- title:
--   Filtered colimits of injective étale sheaves are acyclic on affine schemes
-- statement:
--   Let X be affine and let F be the colimit of a small filtered diagram of injective abelian sheaves on the small étale site of X. Then all positive cohomology groups of F are zero.
-- source:
--   Stacks Project, Lemma 59.51.4, https://stacks.math.columbia.edu/tag/03Q5.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Mathlib.CategoryTheory.ObjectProperty.Ind

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves)
universe u

theorem AlgebraicGeometry.Scheme.filtered_colimit_of_injectives_etale_H_succ_subsingleton
    {J : Type u} [Category.{u} J] [IsFiltered J]
    (X : Scheme.{u}) [IsAffine X] (F : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    [∀ i, Injective (F.obj i)] (d : Cocone F) (_ : IsColimit d) (q : ℕ) :
    Subsingleton (d.pt.H (q + 1)) := by sorry
