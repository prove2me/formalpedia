-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_integrable_w
-- name    : CompanionTheory.D.gk.admitted.Gard.integrable_w
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:07:12.21559+00:00
-- url     : https://prove2.me/theorems/bd11fc22-39c3-41a7-bcfe-67d947391d1c
-- title:
--   Gard: integrable w
-- statement:
--   The Gard construction uses the integrable w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingAvg.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingAvg.lean#L42-L44

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem CompanionTheory.D.gk.admitted.Gard.integrable_w (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) {w : G → ℝ}
    (hw : Continuous w) (hc : HasCompactSupport w) (u : H) : Integrable (fun x => w x • ρ x u) μ := by sorry
