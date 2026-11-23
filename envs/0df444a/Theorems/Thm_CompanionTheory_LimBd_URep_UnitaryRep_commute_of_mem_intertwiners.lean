-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_commute_of_mem_intertwiners
-- name    : CompanionTheory.LimBd.URep.UnitaryRep.commute_of_mem_intertwiners
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:54:41.254329+00:00
-- url     : https://prove2.me/theorems/dc4d01c5-f8a8-4485-a16e-3e994aeadea8
-- title:
--   Unitary Rep: commute of mem intertwiners
-- statement:
--   The Unitary Rep construction uses the commute of mem intertwiners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L239-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L239-L241

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

theorem CompanionTheory.LimBd.URep.UnitaryRep.commute_of_mem_intertwiners {T : H →L[ℂ] H} (hT : T ∈ π.intertwiners π) (g : G) :
    Commute T (π g) := by sorry
