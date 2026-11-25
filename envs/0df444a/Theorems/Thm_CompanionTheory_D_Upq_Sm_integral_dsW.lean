-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_integral_dsW
-- name    : CompanionTheory.D.Upq.Sm.integral_dsW
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:41:48.398766+00:00
-- url     : https://prove2.me/theorems/5c179a24-6529-4060-a0c6-3cdb4dda8776
-- title:
--   Sm: integral ds W
-- statement:
--   The Sm construction uses the integral ds W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L236-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L236-L246

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
variable {hG : IsMatGroup G}
variable [CompleteSpace H]

theorem CompanionTheory.D.Upq.Sm.integral_dsW (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {φ : Mat n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) : ∀ {W : List (Mat n)}, LieW G W →
    ∫ g : MG G hG, φ g.mat • dsW σ W (σ g.mat v) ∂haar =
      ∫ g : MG G hG, LW W φ g.mat • σ g.mat v ∂haar
  := by sorry
