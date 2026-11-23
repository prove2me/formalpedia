-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_exists_avg
-- name    : CompanionTheory.D.gk.admitted.exists_avg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:24.193167+00:00
-- url     : https://prove2.me/theorems/c90f90e9-f616-4e92-9415-8879d88a9d09
-- title:
--   admitted: exists avg
-- statement:
--   The admitted construction uses the exists avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/ExistsAvg.lean#L19-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/ExistsAvg.lean#L19-L32

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_ExistsAvg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
variable {K : Type} [Group K] [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {μ : Measure K} [IsFiniteMeasure μ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : K →* (H →L[ℂ] H)}

theorem CompanionTheory.D.gk.admitted.exists_avg (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hc : ∀ v, Continuous fun x => σ x v) {e : K → ℂ}
    (he : Continuous e) : ∃ E : H →L[ℂ] H, ∀ u, E u = ∫ k, e k • σ k u ∂μ := by sorry
