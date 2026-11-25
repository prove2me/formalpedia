-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_isSm_integral
-- name    : CompanionTheory.D.Upq.Sm.isSm_integral
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:09:42.797454+00:00
-- url     : https://prove2.me/theorems/899067db-519b-534c-a28c-199d3d458cef
-- title:
--   Sm: is Sm integral
-- statement:
--   The Sm construction uses the is Sm integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ParametricIntegralSmoothness/IntCommute.lean#L151-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ParametricIntegralSmoothness/IntCommute.lean#L151-L168

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)} {hG : IsMatGroup G}

theorem CompanionTheory.D.Upq.Sm.isSm_integral (hG : IsMatGroup G) (h : RepOn G σ) {v : H} (hv : IsSm G σ v)
    {μ : Measure (MtM n)} (hμ : IsHaarOnM G μ) {f : MtM n → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) : IsSm G σ (∫ g, f g • σ (Matrix.of g) v ∂μ) := by sorry
