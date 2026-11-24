-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_continuousOn_dsW_orbit
-- name    : CompanionTheory.D.Upq.Sm.continuousOn_dsW_orbit
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:32.144716+00:00
-- url     : https://prove2.me/theorems/f478aa5e-74dc-4ab5-bbe2-d99c6c2429d2
-- title:
--   Sm: continuous On ds W orbit
-- statement:
--   The Sm construction uses the continuous On ds W orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothVec.lean#L231-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothVec.lean#L231-L237

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem CompanionTheory.D.Upq.Sm.continuousOn_dsW_orbit (h : RepOn G σ) {w : H} (hw : IsSm G σ w) {W : List (Mat n)}
    (hW : LieW G W) : ContinuousOn (fun x => dsW σ W (σ x w)) G := by sorry
