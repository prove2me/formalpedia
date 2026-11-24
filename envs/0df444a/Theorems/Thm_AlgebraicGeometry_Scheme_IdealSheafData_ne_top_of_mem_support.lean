-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ne_top_of_mem_support
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.ne_top_of_mem_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:16.048238+00:00
-- url     : https://prove2.me/theorems/b41afe4a-60c1-48e1-8a3e-a442193bd912
-- title:
--   Ideal Sheaf Data: ne top of mem support
-- statement:
--   The Ideal Sheaf Data construction uses the ne top of mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L291-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L291-L297

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

theorem AlgebraicGeometry.Scheme.IdealSheafData.ne_top_of_mem_support (J : Y.IdealSheafData) (x : ↥Y) (hx : x ∈ J.support) : J ≠ ⊤ := by sorry
