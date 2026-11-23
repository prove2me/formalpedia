-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_exists_preimage
-- name    : CompanionTheory.D.gk.admitted.Gard.exists_preimage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:30:41.013498+00:00
-- url     : https://prove2.me/theorems/6435fd97-7235-4997-a182-c07222fad68b
-- title:
--   Gard: exists preimage
-- statement:
--   The Gard construction uses the exists preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingAvg.lean#L137-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingAvg.lean#L137-L147

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard

theorem CompanionTheory.D.gk.admitted.Gard.exists_preimage {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (Y : Submodule ℂ H)
    [FiniteDimensional ℂ Y] (T : H →L[ℂ] H) (hT : ∀ y ∈ Y, T y ∈ Y) (hi : ∀ y ∈ Y, T y = 0 → y = 0) :
    ∀ v ∈ Y, ∃ u, T u = v := by sorry
