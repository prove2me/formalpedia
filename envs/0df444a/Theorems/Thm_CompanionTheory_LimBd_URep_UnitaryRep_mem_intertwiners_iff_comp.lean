-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_mem_intertwiners_iff_comp
-- name    : CompanionTheory.LimBd.URep.UnitaryRep.mem_intertwiners_iff_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:16:05.397591+00:00
-- url     : https://prove2.me/theorems/63184f1b-fbfc-4584-9852-b8f19902ea98
-- title:
--   Unitary Rep: mem intertwiners iff comp
-- statement:
--   The Unitary Rep construction uses the mem intertwiners iff comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L215-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L215-L217

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

theorem CompanionTheory.LimBd.URep.UnitaryRep.mem_intertwiners_iff_comp {T : H →L[ℂ] K} :
    T ∈ π.intertwiners σ ↔ ∀ g : G, T ∘L π g = σ g ∘L T := by sorry
