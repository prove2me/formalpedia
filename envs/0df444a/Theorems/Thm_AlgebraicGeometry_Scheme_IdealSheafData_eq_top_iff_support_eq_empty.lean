-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_top_iff_support_eq_empty
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:06.59102+00:00
-- url     : https://prove2.me/theorems/9bbe35b6-6043-43af-bcbf-1dbe8fc3f54e
-- title:
--   Ideal Sheaf Data: eq top iff support eq empty
-- statement:
--   The Ideal Sheaf Data construction uses the eq top iff support eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L299-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L299-L302

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

theorem AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty {X : Scheme.{u}} (I : X.IdealSheafData) :
    I = ⊤ ↔ (I.support : Set X) = ∅ := by sorry
