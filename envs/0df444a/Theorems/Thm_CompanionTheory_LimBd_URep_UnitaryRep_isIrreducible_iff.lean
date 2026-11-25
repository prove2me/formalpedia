-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_isIrreducible_iff
-- name    : CompanionTheory.LimBd.URep.UnitaryRep.isIrreducible_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:16:10.613896+00:00
-- url     : https://prove2.me/theorems/206c0e0d-7219-4c75-907d-1aeccbdb8eb9
-- title:
--   Unitary Rep: is Irreducible iff
-- statement:
--   The Unitary Rep construction uses the is Irreducible iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepSchur.lean#L107-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepSchur.lean#L107-L127

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepBasic
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_isIrreducible_iff

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

theorem CompanionTheory.LimBd.URep.UnitaryRep.isIrreducible_iff :
    π.IsIrreducible ↔
      Nontrivial H ∧ ∀ T ∈ π.intertwiners π, ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by sorry
