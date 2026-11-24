-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_directImage_baseChange_of_isProper
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_directImage_baseChange_of_isProper
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-24T02:14:42.385486+00:00
-- url     : https://prove2.me/theorems/f6e673c5-a1b4-413b-bab2-b9a9c3a5ba4b
-- title:
--   Ordinary étale direct image for proper maps commutes with base change
-- statement:
--   For a Cartesian square with a proper vertical morphism $f$ and any abelian étale sheaf $F$ on its source, the inverse image of $f_*F$ is isomorphic to the direct image of the inverse image of $F$ on the changed source.
-- source:
--   Stacks Project, Lemma 59.91.5, https://stacks.math.columbia.edu/tag/0A3U.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.nonempty_etale_directImage_baseChange_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {X' Y' : Scheme.{u}} (a : X' ⟶ X) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (h : IsPullback f' a b f) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Nonempty ((PhilipponEtaleSmallSite.pullbackSheaves b).obj ((PhilipponEtaleClosedPushforward.pushforward f).obj F) ≅
      (PhilipponEtaleClosedPushforward.pushforward f').obj ((PhilipponEtaleSmallSite.pullbackSheaves a).obj F)) := by sorry
