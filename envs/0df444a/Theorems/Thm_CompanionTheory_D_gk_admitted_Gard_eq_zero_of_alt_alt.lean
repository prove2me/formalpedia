-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_eq_zero_of_alt_alt
-- name    : CompanionTheory.D.gk.admitted.Gard.eq_zero_of_alt_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:45.032943+00:00
-- url     : https://prove2.me/theorems/60caef29-0ca1-469f-8945-313a5632296d
-- title:
--   Gard: eq zero of alt alt
-- statement:
--   The Gard construction uses the eq zero of alt alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingAvg.lean#L116-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingAvg.lean#L116-L133

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

theorem CompanionTheory.D.gk.admitted.Gard.eq_zero_of_alt_alt (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u)
    {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) (h0 : 0 ≤ w) (h1 : w 1 ≠ 0)
    (y : H) (hy : ∀ x, w x ≠ 0 → ‖ρ x y - y‖ ≤ 1 / 2 * ‖y‖) (hT : ∫ x, w x • ρ x y ∂μ = 0) : y = 0 := by sorry
