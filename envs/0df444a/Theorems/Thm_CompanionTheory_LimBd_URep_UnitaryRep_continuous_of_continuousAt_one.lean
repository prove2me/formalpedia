-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_continuous_of_continuousAt_one
-- name    : CompanionTheory.LimBd.URep.UnitaryRep.continuous_of_continuousAt_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:15:50.318646+00:00
-- url     : https://prove2.me/theorems/0e8cd4ff-5355-5c34-af92-0104109f0aee
-- title:
--   Unitary Rep: continuous of continuous At one
-- statement:
--   The Unitary Rep construction uses the continuous of continuous At one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L111-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/URepBasic.lean#L111-L132

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

theorem CompanionTheory.LimBd.URep.UnitaryRep.continuous_of_continuousAt_one [IsTopologicalGroup G] (ρ : G →* unitary (H →L[ℂ] H))
    (hρ : ∀ v : H, ContinuousAt (fun g => (ρ g : H →L[ℂ] H) v) 1) (v : H) :
    Continuous fun g => (ρ g : H →L[ℂ] H) v := by sorry
