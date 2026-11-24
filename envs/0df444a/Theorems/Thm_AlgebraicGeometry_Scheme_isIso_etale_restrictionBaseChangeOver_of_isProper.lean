-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isIso_etale_restrictionBaseChangeOver_of_isProper
-- name    : AlgebraicGeometry.Scheme.isIso_etale_restrictionBaseChangeOver_of_isProper
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-24T05:10:21.873148+00:00
-- url     : https://prove2.me/theorems/248ec977-a92f-4a5c-b8ca-32f3c91da4d5
-- title:
--   Canonical ordinary étale base change for a proper morphism
-- statement:
--   In a Cartesian square whose vertical maps are proper, the canonical map from the pullback of the direct image to the direct image of the pullback is invertible for every abelian étale sheaf.
-- source:
--   Stacks Project, Lemma 59.91.5, https://stacks.math.columbia.edu/tag/0A3U.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.isIso_etale_restrictionBaseChangeOver_of_isProper
    {X Y S T : Scheme.{u}} (p : Y ⟶ X) [IsProper p]
    (i : S ⟶ X) (p₀ : T ⟶ S) (j : T ⟶ Y) (h : IsPullback p₀ j i p)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (PhilipponEtalePullbackSquareUnits.restrictionBaseChangeOver i p p₀ j (p₀ ≫ i) rfl h.w.symm F) := by sorry
