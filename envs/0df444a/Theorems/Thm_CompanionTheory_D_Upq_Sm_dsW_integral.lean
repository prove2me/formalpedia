-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_integral
-- name    : CompanionTheory.D.Upq.Sm.dsW_integral
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:01:11.681643+00:00
-- url     : https://prove2.me/theorems/61a29944-68c6-4389-b034-a5caeef499a1
-- title:
--   Sm: ds W integral
-- statement:
--   The Sm construction uses the ds W integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ParametricIntegralSmoothness/IntCommute.lean#L68-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ParametricIntegralSmoothness/IntCommute.lean#L68-L92

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
variable {μ : Measure (MG G hG)} [IsFiniteMeasureOnCompacts μ] {φ : MG G hG → ℂ}

theorem CompanionTheory.D.Upq.Sm.dsW_integral (h : RepOn G σ) {v : H} (hv : IsSm G σ v) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) : ∀ {W : List (Mat n)}, LieW G W →
    dsW σ W (∫ g, φ g • σ g.mat v ∂μ) = ∫ g, φ g • dsW σ W (σ g.mat v) ∂μ
  := by sorry
