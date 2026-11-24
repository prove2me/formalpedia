-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_mem_support_iff_ideal_le_primeIdealOf
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_ideal_le_primeIdealOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:15.345896+00:00
-- url     : https://prove2.me/theorems/3658222e-479a-4f23-bdfc-6ff083f0b700
-- title:
--   Ideal Sheaf Data: mem support iff ideal le prime Ideal Of
-- statement:
--   The Ideal Sheaf Data construction uses the mem support iff ideal le prime Ideal Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L337-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean#L337-L351

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

theorem AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_ideal_le_primeIdealOf {X : Scheme.{u}} (I : X.IdealSheafData)
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    x ∈ I.support ↔ I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by sorry
