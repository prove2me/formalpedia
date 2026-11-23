-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_contDiff_integral_comp
-- name    : CompanionTheory.D.gk.admitted.Gard.contDiff_integral_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:53.409895+00:00
-- url     : https://prove2.me/theorems/e55470c4-28d3-4ff1-a9b6-86e13d4cd3ff
-- title:
--   Gard: cont Diff integral comp
-- statement:
--   The Gard construction uses the cont Diff integral comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Garding.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Garding.lean#L19-L29

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingBump
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open CompanionTheory.D.gk.admitted.Gard

theorem CompanionTheory.D.gk.admitted.Gard.contDiff_integral_comp {P Q E α : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace α] [T2Space α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasureOnCompacts μ] (Φ : P × Q → E) (hΦ : ContDiff ℝ ∞ Φ) (q : α → Q)
    (hq : Continuous q)
    (hsupp : ∀ y₀ : P, ∃ U ∈ 𝓝 y₀, ∃ C : Set α, IsCompact C ∧ ∀ y ∈ U, ∀ a ∉ C, Φ (y, q a) = 0) :
    ContDiff ℝ ∞ fun y => ∫ a, Φ (y, q a) ∂μ := by sorry
