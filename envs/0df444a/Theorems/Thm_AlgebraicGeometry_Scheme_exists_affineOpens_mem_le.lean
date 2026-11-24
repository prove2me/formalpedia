-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem_le
-- name    : AlgebraicGeometry.Scheme.exists_affineOpens_mem_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:22.402979+00:00
-- url     : https://prove2.me/theorems/317be123-b3d9-46d9-ae1d-2a733dffc106
-- title:
--   Scheme: exists affine Opens mem le
-- statement:
--   The Scheme construction uses the exists affine Opens mem le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/AffineOpens.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/AffineOpens.lean#L21-L25

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

theorem AlgebraicGeometry.Scheme.exists_affineOpens_mem_le {X : Scheme.{u}} {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ U := by sorry
