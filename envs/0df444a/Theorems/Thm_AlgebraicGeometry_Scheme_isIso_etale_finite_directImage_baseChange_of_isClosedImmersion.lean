-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isIso_etale_finite_directImage_baseChange_of_isClosedImmersion
-- name    : AlgebraicGeometry.Scheme.isIso_etale_finite_directImage_baseChange_of_isClosedImmersion
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-25T00:29:51.481887+00:00
-- url     : https://prove2.me/theorems/28322e66-ade4-457e-a03f-01b9dde92562
-- title:
--   Finite étale direct image commutes with restriction to a closed subscheme
-- statement:
--   In a Cartesian square with vertical maps $p:Y\to X$ and
--       $p_0:W\to Z$, let $p$ be finite and the bottom map $i:Z\hookrightarrow X$ a closed immersion.
--       For every abelian étale sheaf $F$ on $Y$, the canonical comparison
--       $i^*p_*F\to p_{0,*}j^*F$ is an isomorphism, where $j:W\to Y$ is the upper map.
-- source:
--   Closed-base case of Stacks Project, Lemma 59.55.3, https://stacks.math.columbia.edu/tag/0959.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Mathlib.AlgebraicGeometry.Morphisms.Finite

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtalePullbackSquareUnits (restrictionBaseChangeOver)
universe u

theorem AlgebraicGeometry.Scheme.isIso_etale_finite_directImage_baseChange_of_isClosedImmersion
    {X Z Y W : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (p : Y ⟶ X) [IsFinite p] (p₀ : W ⟶ Z) (j : W ⟶ Y) (h : IsPullback p₀ j i p)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (restrictionBaseChangeOver i p p₀ j (p₀ ≫ i) rfl h.w.symm F) := by sorry
