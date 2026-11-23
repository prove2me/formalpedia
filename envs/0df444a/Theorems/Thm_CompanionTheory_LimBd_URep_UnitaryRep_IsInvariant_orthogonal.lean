-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsInvariant_orthogonal
-- name    : CompanionTheory.LimBd.URep.UnitaryRep.IsInvariant.orthogonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:48.114895+00:00
-- url     : https://prove2.me/theorems/77334a79-85d2-434f-9f23-ccfcb0e0a45f
-- title:
--   Is Invariant: orthogonal
-- statement:
--   The Is Invariant construction uses the orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L167-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L167-L171

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.URep
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap Filter Topology
open CompanionTheory.LimBd.URep.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (π : UnitaryRep G H)
variable {π}

theorem CompanionTheory.LimBd.URep.UnitaryRep.IsInvariant.orthogonal {V : Submodule ℂ H} (hV : π.IsInvariant V) :
    π.IsInvariant Vᗮ := by sorry
