-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_Equiv_mem_intertwiners
-- name    : CompanionTheory.LimBd.URep.UnitaryRep.Equiv.mem_intertwiners
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:15:54.570826+00:00
-- url     : https://prove2.me/theorems/8df40ceb-0986-46f6-8e6d-ccedd672765a
-- title:
--   Equiv: mem intertwiners
-- statement:
--   The Equiv construction uses the mem intertwiners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L285-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L285-L286

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
open CompanionTheory.LimBd.URep.UnitaryRep.Equiv

theorem CompanionTheory.LimBd.URep.UnitaryRep.Equiv.mem_intertwiners (e : π.Equiv σ) :
    (e.toLinearIsometryEquiv : H →L[ℂ] K) ∈ π.intertwiners σ := by sorry
