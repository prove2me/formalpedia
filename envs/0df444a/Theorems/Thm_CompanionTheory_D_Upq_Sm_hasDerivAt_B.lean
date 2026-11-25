-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_hasDerivAt_B
-- name    : CompanionTheory.D.Upq.Sm.hasDerivAt_B
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:42:41.10083+00:00
-- url     : https://prove2.me/theorems/526b20ab-9170-42f5-9199-05953c16a7d8
-- title:
--   Sm: has Deriv At B
-- statement:
--   The Sm construction uses the has Deriv At B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L215-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L215-L234

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

theorem CompanionTheory.D.Upq.Sm.hasDerivAt_B (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {X : Mat n} (hX : ∀ t, ex X t ∈ G)
    {W : List (Mat n)} (hW : LieW G W) {φ : Mat n → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) :
    HasDerivAt (fun t => σ (ex X t) (∫ g : MG G hG, φ g.mat • dsW σ W (σ g.mat v) ∂haar))
      (∫ g : MG G hG, φ g.mat • dsW σ (X :: W) (σ g.mat v) ∂haar) 0 := by sorry
