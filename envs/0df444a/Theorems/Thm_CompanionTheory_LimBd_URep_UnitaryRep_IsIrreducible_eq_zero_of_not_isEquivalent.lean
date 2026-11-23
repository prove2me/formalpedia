-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsIrreducible_eq_zero_of_not_isEquivalent
-- name    : CompanionTheory.LimBd.URep.UnitaryRep.IsIrreducible.eq_zero_of_not_isEquivalent
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:46.856898+00:00
-- url     : https://prove2.me/theorems/2e01be44-243d-44a7-94f2-2c8720581977
-- title:
--   Is Irreducible: eq zero of not is Equivalent
-- statement:
--   The Is Irreducible construction uses the eq zero of not is Equivalent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepSchur.lean#L198-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepSchur.lean#L198-L201

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

theorem CompanionTheory.LimBd.URep.UnitaryRep.IsIrreducible.eq_zero_of_not_isEquivalent (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible)
    (hne : ¬ π.IsEquivalent σ) {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) : T = 0 := by sorry
