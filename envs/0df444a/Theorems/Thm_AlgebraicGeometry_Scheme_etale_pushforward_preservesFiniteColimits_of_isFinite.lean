-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_etale_pushforward_preservesFiniteColimits_of_isFinite
-- name    : AlgebraicGeometry.Scheme.etale_pushforward_preservesFiniteColimits_of_isFinite
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-21T16:15:27.254874+00:00
-- url     : https://prove2.me/theorems/ce4cd55a-b295-4ef9-94cb-40d26a5c4141
-- title:
--   Finite direct image is exact on abelian étale sheaves
-- statement:
--   Let $p\colon Y\to X$ be a finite morphism of schemes. The direct-image functor from abelian sheaves on the small étale site of $Y$ to abelian sheaves on the small étale site of $X$ preserves finite colimits. It also preserves finite limits by its right adjoint structure.
-- source:
--   Stacks Project, Proposition 59.55.2, https://stacks.math.columbia.edu/tag/03QP.

import Definitions.Def_AlgebraicGeometry_SmallEtaleAbelianDirectImage
import Mathlib.AlgebraicGeometry.Morphisms.Finite

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.etale_pushforward_preservesFiniteColimits_of_isFinite
    {X Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] :
    PreservesFiniteColimits (PhilipponEtaleClosedPushforward.pushforward p) := by sorry
