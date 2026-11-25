-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_subtypeL_mem_intertwiners
-- name    : CompanionTheory.LimBd.URep.UnitaryRep.subtypeL_mem_intertwiners
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:20.329352+00:00
-- url     : https://prove2.me/theorems/1c09d137-0fbe-4491-ae37-95a5a276e94c
-- title:
--   Unitary Rep: subtype L mem intertwiners
-- statement:
--   The Unitary Rep construction uses the subtype L mem intertwiners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L357-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L357-L358

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
variable (π) (V : Submodule ℂ H) [CompleteSpace V] (hV : π.IsInvariant V)

theorem CompanionTheory.LimBd.URep.UnitaryRep.subtypeL_mem_intertwiners : V.subtypeL ∈ (π.restrict V hV).intertwiners π := by sorry
