-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_support_nonempty_iff_ne_top
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.support_nonempty_iff_ne_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:41.652418+00:00
-- url     : https://prove2.me/theorems/ba8c35a4-fbd5-4b0b-b8c3-a4a286559e6e
-- title:
--   Ideal Sheaf Data: support nonempty iff ne top
-- statement:
--   The Ideal Sheaf Data construction uses the support nonempty iff ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L304-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L304-L306

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

theorem AlgebraicGeometry.Scheme.IdealSheafData.support_nonempty_iff_ne_top {X : Scheme.{u}} (I : X.IdealSheafData) :
    (I.support : Set X).Nonempty ↔ I ≠ ⊤ := by sorry
