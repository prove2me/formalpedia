-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_mul_mem_intertwiners
-- name    : CompanionTheory.LimBd.URep.UnitaryRep.mul_mem_intertwiners
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:16:09.351663+00:00
-- url     : https://prove2.me/theorems/ba094c7c-d83b-418a-abcd-50966ebe7085
-- title:
--   Unitary Rep: mul mem intertwiners
-- statement:
--   The Unitary Rep construction uses the mul mem intertwiners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L225-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L225-L226

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

theorem CompanionTheory.LimBd.URep.UnitaryRep.mul_mem_intertwiners {S T : H →L[ℂ] H} (hS : S ∈ π.intertwiners π)
    (hT : T ∈ π.intertwiners π) : S * T ∈ π.intertwiners π := by sorry
