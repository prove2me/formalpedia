-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_inner_map_left
-- name    : CompanionTheory.LimBd.URep.UnitaryRep.inner_map_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:48.535338+00:00
-- url     : https://prove2.me/theorems/0bc8d598-e64d-406f-b3b1-06be9b40bdfe
-- title:
--   Unitary Rep: inner map left
-- statement:
--   The Unitary Rep construction uses the inner map left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L67-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L67-L68

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

theorem CompanionTheory.LimBd.URep.UnitaryRep.inner_map_left (g : G) (v w : H) : ⟪π g v, w⟫_ℂ = ⟪v, π g⁻¹ w⟫_ℂ := by sorry
