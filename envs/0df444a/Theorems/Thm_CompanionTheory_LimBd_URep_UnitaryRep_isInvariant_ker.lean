-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_isInvariant_ker
-- name    : CompanionTheory.LimBd.URep.UnitaryRep.isInvariant_ker
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:16:11.200312+00:00
-- url     : https://prove2.me/theorems/adde4fb1-660d-48fe-9c73-433729fe7d78
-- title:
--   Unitary Rep: is Invariant ker
-- statement:
--   The Unitary Rep construction uses the is Invariant ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L253-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L253-L257

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
variable {σ : UnitaryRep G K} {τ : UnitaryRep G L}

theorem CompanionTheory.LimBd.URep.UnitaryRep.isInvariant_ker {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) :
    π.IsInvariant (LinearMap.ker (T : H →ₗ[ℂ] K)) := by sorry
