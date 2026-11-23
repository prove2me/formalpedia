-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- name    : CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:07:00.563802+00:00
-- url     : https://prove2.me/theorems/91c3a8f7-0dc8-4bf7-b3ab-29d2c088634e
-- title:
--   Unitary Rep: coe restrict apply
-- statement:
--   The Unitary Rep construction uses the coe restrict apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L354-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L354-L355

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

theorem CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply (g : G) (v : V) :
    ((π.restrict V hV g v : V) : H) = π g v := by sorry

attribute [defeq] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply
