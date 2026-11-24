-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_listProd
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.comap_listProd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:00.403798+00:00
-- url     : https://prove2.me/theorems/c1d320cf-715a-42bc-9c86-9ccb30a96d30
-- title:
--   Ideal Sheaf Data: comap list Prod
-- statement:
--   The Ideal Sheaf Data construction uses the comap list Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L366-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L366-L372

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}

theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_listProd {X Y : Scheme.{u}} (f : X ⟶ Y) (L : List Y.IdealSheafData) :
    L.prod.comap f = (L.map (·.comap f)).prod := by sorry
