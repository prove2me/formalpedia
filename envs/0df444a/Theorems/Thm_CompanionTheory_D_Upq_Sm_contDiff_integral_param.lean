-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_contDiff_integral_param
-- name    : CompanionTheory.D.Upq.Sm.contDiff_integral_param
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:08:18.581798+00:00
-- url     : https://prove2.me/theorems/68ee0890-d67b-4f21-a117-a6c675174ed0
-- title:
--   Sm: cont Diff integral param
-- statement:
--   The Sm construction uses the cont Diff integral param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ParametricIntegralSmoothness/IntCommute.lean#L29-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ParametricIntegralSmoothness/IntCommute.lean#L29-L52

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

theorem CompanionTheory.D.Upq.Sm.contDiff_integral_param {P E V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] {f : E → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    {F : P × E → V} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ fun p => ∫ t, f t • F (p, t) ∂μ := by sorry
