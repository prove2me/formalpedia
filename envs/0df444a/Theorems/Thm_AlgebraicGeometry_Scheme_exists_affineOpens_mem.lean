-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem
-- name    : AlgebraicGeometry.Scheme.exists_affineOpens_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:15.221825+00:00
-- url     : https://prove2.me/theorems/66b3c535-459b-4931-8130-206726b3d6b9
-- title:
--   Scheme: exists affine Opens mem
-- statement:
--   The Scheme construction uses the exists affine Opens mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/AffineOpens.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/AffineOpens.lean#L14-L19

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.exists_affineOpens_mem {X : Scheme.{u}} (x : X) : ∃ U : X.affineOpens, x ∈ U.1 := by sorry
