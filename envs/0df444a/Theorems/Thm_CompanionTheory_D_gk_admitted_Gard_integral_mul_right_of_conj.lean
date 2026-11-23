-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_integral_mul_right_of_conj
-- name    : CompanionTheory.D.gk.admitted.Gard.integral_mul_right_of_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:16.182921+00:00
-- url     : https://prove2.me/theorems/6b417438-8ae0-4a5a-9294-25e86fd7c435
-- title:
--   Gard: integral mul right of conj
-- statement:
--   The Gard construction uses the integral mul right of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingAvg.lean#L63-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingAvg.lean#L63-L78

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

theorem CompanionTheory.D.gk.admitted.Gard.integral_mul_right_of_conj {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) (h0 : 0 ≤ w)
    (h1 : w 1 ≠ 0) (k : G) (hk : ∀ x, w (k⁻¹ * x * k) = w x) (F : G → H) :
    ∫ x, F (x * k) ∂μ = ∫ x, F x ∂μ := by sorry
