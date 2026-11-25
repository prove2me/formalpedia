-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_URep_integrable_pairing
-- name    : CompanionTheory.LimBd.URep.integrable_pairing
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:25.326591+00:00
-- url     : https://prove2.me/theorems/3ba0e172-59ab-4151-917a-294a6b8472c4
-- title:
--   URep: integrable pairing
-- statement:
--   The URep construction uses the integrable pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurOrthogonality.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurOrthogonality.lean#L68-L70

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.URep
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem CompanionTheory.LimBd.URep.integrable_pairing {π : UnitaryRep G H} {σ : UnitaryRep G K} (hπ : SqInt μ π) (hσ : SqInt μ σ)
    (v w : H) (v' w' : K) : Integrable (fun g => ⟪w, π g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ := by sorry
