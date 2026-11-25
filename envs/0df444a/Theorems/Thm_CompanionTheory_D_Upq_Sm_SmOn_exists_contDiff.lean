-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_exists_contDiff
-- name    : CompanionTheory.D.Upq.Sm.SmOn.exists_contDiff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:01:29.674015+00:00
-- url     : https://prove2.me/theorems/af187211-41cf-4655-b694-56bbb7e822f8
-- title:
--   Sm On: exists cont Diff
-- statement:
--   The Sm On construction uses the exists cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ParametricIntegralSmoothness/IntCommute.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ParametricIntegralSmoothness/IntCommute.lean#L15-L27

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_Exists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ParametricIntegralSmoothness_IntCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff Manifold Convolution
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx

theorem CompanionTheory.D.Upq.Sm.SmOn.exists_contDiff {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] {A : Set E} {f : E → V}
    (hf : SmOn A f) (hA : IsClosed A) : ∃ F : E → V, ContDiff ℝ ∞ F ∧ ∀ a ∈ A, F a = f a := by sorry
