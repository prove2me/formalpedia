-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_mem_support_comap
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:05.831033+00:00
-- url     : https://prove2.me/theorems/f0bdd316-bb79-4573-8cde-0d02384b983e
-- title:
--   Ideal Sheaf Data: mem support comap
-- statement:
--   The Ideal Sheaf Data construction uses the mem support comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L281-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L281-L289

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

theorem AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap {f : X ⟶ Y} {I : Y.IdealSheafData} {x : X} :
    x ∈ (I.comap f).support ↔ f.base x ∈ I.support := by sorry
