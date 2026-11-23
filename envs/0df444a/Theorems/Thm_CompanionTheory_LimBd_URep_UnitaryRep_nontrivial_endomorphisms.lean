-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_nontrivial_endomorphisms
-- name    : CompanionTheory.LimBd.URep.UnitaryRep.nontrivial_endomorphisms
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:54:44.353625+00:00
-- url     : https://prove2.me/theorems/25950eb1-c87c-4a28-9fab-d2082c873541
-- title:
--   Unitary Rep: nontrivial endomorphisms
-- statement:
--   The Unitary Rep construction uses the nontrivial endomorphisms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepSchur.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepSchur.lean#L19-L21

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepBasic
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.URep
open CompanionTheory.LimBd.URep.UnitaryRep
open scoped InnerProductSpace ComplexConjugate
open scoped ComplexStarModule
open ContinuousLinearMap Complex
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {σ : UnitaryRep G K}
omit [CompleteSpace H]

theorem CompanionTheory.LimBd.URep.UnitaryRep.nontrivial_endomorphisms [Nontrivial H] : Nontrivial (H →L[ℂ] H) := by sorry
