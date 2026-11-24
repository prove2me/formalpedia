-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem
-- name    : AlgebraicGeometry.Scheme.exists_isAffineOpen_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:56.751139+00:00
-- url     : https://prove2.me/theorems/ae59b7e4-5e37-49ae-907e-c363d74d4993
-- title:
--   Scheme: exists is Affine Open mem
-- statement:
--   The Scheme construction uses the exists is Affine Open mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/AffineOpens.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/AffineOpens.lean#L7-L12

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

theorem AlgebraicGeometry.Scheme.exists_isAffineOpen_mem {X : Scheme.{u}} (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U := by sorry
