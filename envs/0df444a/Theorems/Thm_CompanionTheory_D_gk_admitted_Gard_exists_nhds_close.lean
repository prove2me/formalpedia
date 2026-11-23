-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_exists_nhds_close
-- name    : CompanionTheory.D.gk.admitted.Gard.exists_nhds_close
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:48.640849+00:00
-- url     : https://prove2.me/theorems/9b2ed63f-5807-44d3-bb3a-ce30457d7436
-- title:
--   Gard: exists nhds close
-- statement:
--   The Gard construction uses the exists nhds close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingAvg.lean#L100-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingAvg.lean#L100-L114

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

theorem CompanionTheory.D.gk.admitted.Gard.exists_nhds_close (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) (h1 : ∀ u, ρ 1 u = u)
    (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] :
    ∃ V ∈ 𝓝 (1 : G), ∀ x ∈ V, ∀ y ∈ Y, ‖ρ x y - y‖ ≤ 1 / 2 * ‖y‖ := by sorry
