-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_iSup
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.comap_iSup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:09.570683+00:00
-- url     : https://prove2.me/theorems/17289136-477d-4463-8287-47e8993055b9
-- title:
--   Ideal Sheaf Data: comap i Sup
-- statement:
--   The Ideal Sheaf Data construction uses the comap i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L209-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L209-L211

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

theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_iSup {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Sort*} (I : ι → Y.IdealSheafData) :
    (⨆ i, I i).comap f = ⨆ i, (I i).comap f := by sorry
